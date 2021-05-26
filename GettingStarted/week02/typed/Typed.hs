{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Week02.Typed where

import           Control.Monad        hiding (fmap)
import           Data.Map             as Map
import           Data.Text            (Text)
import           Data.Void            (Void)
import           Plutus.Contract      hiding (when)
import           PlutusTx             (Data (..))
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Scripts       as Scripts
import qualified Ledger.Typed.Scripts as Scripts -- Ledger.Typed.Scripts is imported to use boilerplate code () -> Integer -> ValidatorCtx -> Bool on line 33
import           Ledger.Ada           as Ada
import           Playground.Contract  (printJson, printSchemas, ensureKnownCurrencies, stage)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (Semigroup (..))
import           Text.Printf          (printf)

{-# INLINABLE mkValidator #-}
mkValidator :: () -> Integer -> ValidatorCtx -> Bool -- We replaced the type data with more suitable types
-- We ignored the Datum and instead replaced Data with unit ()
-- For the redeemer we only deal with Integers 
-- we can use the ValidatorCtx as the context
-- We will use the Bool because it always expects to be true or false to succeed
mkValidator () r _ -- The datum is replaced with unit here and 'r' is now type Integer and we ignore the context
    | r == 42   = True -- We can just check if r == 42 to check if redeemer is true now and not use r == I 42 
    | otherwise = False -- Or if the redeemer is false

-- This is no longer type correct and there are different types

-- Next we use haskell type level programming 

data Typed -- Here we define the new data type without any constructors
-- We never use this data type but only use it for the type system
instance Scripts.ScriptType Typed where
    -- Above we just tell the compiler which types it should used for Datum and redeemers
    type instance DatumType Typed = () -- we declare that we choose to use unit () as the datum type on line 33
    type instance RedeemerType Typed = Integer -- we declare that we choose to use Integer as the redeemer type on line 33


inst :: Scripts.ScriptInstance Typed -- the plutus ScriptInstance carries the Typed information of unit () Datum and Integer Redeemer from above
inst = Scripts.validator @Typed -- validator takes 3 arguments
-- @ tell the compiler what type we are using in line 46
    $$(PlutusTx.compile [|| mkValidator ||]) -- argument is the mkValidatorScript $$(PlutusTx.compile [|| mkValidator ||]) :: this will always remain the same
    $$(PlutusTx.compile [|| wrap ||]) -- tells the compiler how to get from this typed version to an untyped version :: this will always remain the same
  where
    wrap = Scripts.wrapValidator @() @Integer -- We define the wrap from line 58 by telling it what types it should use

validator :: Validator
validator = Scripts.validatorScript inst -- the validator script accepts the inst from line 54 and not $$(PlutusTx.compile [|| mkValidator ||])

valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash validator

scrAddress :: Ledger.Address
scrAddress = ScriptAddress valHash

type GiftSchema =
    BlockchainActions
        .\/ Endpoint "give" Integer
        .\/ Endpoint "grab" Integer

give :: (HasBlockchainActions s, AsContractError e) => Integer -> Contract w s e ()
give amount = do
    let tx = mustPayToTheScript () $ Ada.lovelaceValueOf amount -- the mustPayToTheScript is made for this typed version and we can simply just use datum type unit()
    ledgerTx <- submitTxConstraints inst tx -- We replace the submitTx with submitTxConstraints and use the 'inst' argument from line 54
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "made a gift of %d lovelace" amount

grab :: forall w s e. (HasBlockchainActions s, AsContractError e) => Integer -> Contract w s e ()
grab r = do
    utxos <- utxoAt scrAddress
    let orefs   = fst <$> Map.toList utxos
        lookups = Constraints.unspentOutputs utxos      <>
                  Constraints.otherScript validator
        tx :: TxConstraints Void Void
        tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ I r | oref <- orefs]
    ledgerTx <- submitTxConstraintsWith @Void lookups tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "collected gifts"

endpoints :: Contract () GiftSchema Text ()
endpoints = (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" >>= give
    grab' = endpoint @"grab" >>= grab

mkSchemaDefinitions ''GiftSchema

mkKnownCurrencies []

{- We have turned the untyped version that taked mkValidator :: Data -> Data -> Data -> () to a typed version that takes mkValidator :: () -> Integer -> ValidatorCtx -> Bool -}
{- Custom Types for Datum, Redeemer, and the context -}

{- In a realistic smart contracts it is much better to use custom made data types -}
{- ********************************************************************************* -}

-- this will give the same results as the FortyTwo.hs file
