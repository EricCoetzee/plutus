{- First Real World contract -}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Week03.Vesting where

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.Map             as Map
import           Data.Text            (Text)
import           Data.Void            (Void)
import           GHC.Generics         (Generic)
import           Plutus.Contract      hiding (when)
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Playground.Contract  (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (Semigroup (..))
import           Text.Printf          (printf)

data VestingDatum = VestingDatum
    { beneficiary :: PubKeyHash --The entity that can access the $ada and can be identified by the public key
    , deadline    :: Slot
    } deriving Show

PlutusTx.unstableMakeIsData ''VestingDatum

{-# INLINABLE mkValidator #-}
mkValidator :: VestingDatum -> () -> ScriptContext -> Bool --ValidatorCtx now ScriptContext found in (~/plutus/plutus-ledger-api/src/Plutus/V1/Ledger/Context.hs) and we don't need anything information in redeemer because all the information that we need regarding the time and entity that collects is contained in the context that is why we can use VestingDatum from above for the Datum and the redeemer can be unit
mkValidator dat () ctx =
-- Datum name is now dat 
-- we need ctx for the context 
-- we need to check 2 conditions 
-- ** 1 that only the beneficiary can access and unlock thats is UTXO sitting at this Address 
-- By check this by looking if the beneficiary signature is included in this transaction) 
-- ** 2 we also need to check the timing 
-- By checking if this transaction is only executed after the deadline has been reached
    traceIfFalse "beneficiary's signature missing" checkSig      && -- for checking signature
    traceIfFalse "deadline not reached"            checkDeadline  -- for checking if deadline (Slot) has been reached 
     -- The two conditions above is written but not implemented :: connected with '&&'
    -- traceIfFalse "Message" helps with debugging
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx
    -- found in (~/plutus/plutus-ledger-api/src/Plutus/V1/Ledger/Context.hs) :: data ScriptContext = ScriptContext{scriptContextTxInfo :: 'TxInfo', scriptContextPurpose :: ScriptPurpose }
    -- linking ctx to ScriptContext

    checkSig :: Bool -- helper function true or false from above
    checkSig = beneficiary dat `elem` txInfoSignatories info
     -- checking to see if the beneficiary's public hash/Address can be found
    -- txInfoSignatories gives us the [PubKeyHash]
    -- found in (~/plutus/plutus-ledger-api/src/Plutus/V1/Ledger/Context.hs) TxInfo = TxInfo { , txInfoSignatories } 

    checkDeadline :: Bool -- helper function true or false from above
    checkDeadline = from (deadline dat) `contains` txInfoValidRange info -- the txInfoValidRange if checked first to help us add the transaction after the deadline
     -- We have to make certain that this transaction is submitted only after the deadline has been reached
        -- from is like a method for run from a number to infinity
        -- `contains` help us see if the is from the deadline or contains a slot from the deadline (in our case it is txInfoValidRange which is the range of all slots) 
        -- from is Interval {ivFrom = LowerBound (Finite {- lowerBound is Finite -}(Slot {getSlot = 20})) True, ivTo = UpperBound PosInf True {- upperBound is infinite -}}
        -- from is found in (~/plutus/plutus-ledger-api/src/Plutus/V1/Ledger/Context.hs)
        -- txInfoValidRange gives us SlotRange 
        -- all slots must be after the deadline :: txInfoValidRange must be included in the interval that starts the deadline and goes until the end of time <- one way of doing it
        -- we don't know what the time is but we do know that the current time falls into the txInfoValidRange info field
        -- implementation of CheckSig and checkDeadline

data Vesting
instance Scripts.ScriptType Vesting where
    type instance DatumType Vesting = VestingDatum -- the datum type is now VestingDatum from above
    type instance RedeemerType Vesting = () -- the redeemer type is now unit () from above

inst :: Scripts.ScriptInstance Vesting
inst = Scripts.validator @Vesting 
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @VestingDatum @()

validator :: Validator
validator = Scripts.validatorScript inst

scrAddress :: Ledger.Address
scrAddress = scriptAddress validator

data GiveParams = GiveParams -- 3 parameters are needed  for the give
    { gpBeneficiary :: !PubKeyHash  -- the person that gives the amount
    , gpDeadline    :: !Slot -- the deadline 
    , gpAmount      :: !Integer -- the amount
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type VestingSchema =
    BlockchainActions
        .\/ Endpoint "give" GiveParams
        .\/ Endpoint "grab" () -- the grab doens't need any parameters

give :: (HasBlockchainActions s, AsContractError e) => GiveParams -> Contract w s e () --GiveParams can be found above
give gp = do
    let dat = VestingDatum -- compute the datum making dat VestingDatum
                { beneficiary = gpBeneficiary gp 
                , deadline    = gpDeadline gp
                }
        tx  = mustPayToTheScript dat $ Ada.lovelaceValueOf $ gpAmount gp -- paying with the script to the datum and specifying the amount
    ledgerTx <- submitTxConstraints inst tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "made a gift of %d lovelace to %s with deadline %s"
        (gpAmount gp)
        (show $ gpBeneficiary gp)
        (show $ gpDeadline gp)
{- We see grab gets a little more involved because the grab function needs to find all the UTXOs that can be consume -}
grab :: forall w s e. (HasBlockchainActions s, AsContractError e) => Contract w s e ()
grab = do
    now   <- currentSlot -- from the wallet we have access to the current time
    pkh   <- pubKeyHash <$> ownPubKey -- access to our own publichey from the wallet
    utxos <- Map.filter (isSuitable pkh now) <$> utxoAt scrAddress
    if Map.null utxos -- if there is no UTXO available the transaction wont be submitted
        then logInfo @String $ "no gifts available"
        else do
            let orefs   = fst <$> Map.toList utxos
                lookups = Constraints.unspentOutputs utxos  <>
                          Constraints.otherScript validator
                tx :: TxConstraints Void Void
                tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toData () | oref <- orefs] <>
                          mustValidateIn (from now) -- by defealt this is 'always' found in (~/plutus/plutus-ledger-api/src/Plutus/V1/Ledger/Interval.hs)
            ledgerTx <- submitTxConstraintsWith @Void lookups tx
            void $ awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "collected gifts"
  where
    isSuitable :: PubKeyHash -> Slot -> TxOutTx -> Bool -- helper function for looking at the UTXO and applies a filter to the entries and only keeps those that are available now
    isSuitable pkh now o = case txOutDatumHash $ txOutTxOut o of -- getting the publickey hash of the wallet and the current time
        Nothing -> False
        Just h  -> case Map.lookup h $ txData $ txOutTxTx o of -- trying to deserialize the DatumHash 
            Nothing        -> False
            Just (Datum e) -> case PlutusTx.fromData e of
                Nothing -> False
                Just d  -> beneficiary d == pkh && deadline d <= now -- checks that the beneficiary has the publickey to the wallet and is the deadline doens't lay in the future

endpoints :: Contract () VestingSchema Text ()
endpoints = (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" >>= give
    grab' = endpoint @"grab" >>  grab

mkSchemaDefinitions ''VestingSchema

mkKnownCurrencies []
