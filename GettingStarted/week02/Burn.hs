{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-} -- An additional prelude added for Plutus to prevent the normal haskell prelude to be loaded by defealt
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Week02.Gift where

-- imports

import           Control.Monad       hiding (fmap)
import           Data.Map            as Map
import           Data.Text           (Text)
import           Data.Void           (Void)
import           Plutus.Contract     hiding (when)
import           PlutusTx            (Data (..))
import qualified PlutusTx
import           PlutusTx.Prelude    hiding (Semigroup(..), unless) -- only takes unit ()
-- Above we add the Plutus Prelude
import           Ledger              hiding (singleton)
import           Ledger.Constraints  as Constraints
import qualified Ledger.Scripts      as Scripts
import           Ledger.Ada          as Ada
import           Playground.Contract (printJson, printSchemas, ensureKnownCurrencies, stage)
import           Playground.TH       (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types    (KnownCurrency (..))
import           Prelude             (Semigroup (..)) -- only importing the Semigroup that only takes a string
-- Haskell Prelude is a module that is always imported by default
import           Text.Printf         (printf)

-- Start of Validator script

{-# INLINABLE mkValidator #-} -- makes an inlinable helper function
-- {-# INLINABLE mkValidator #-} enable us to use all mkValidator :: Data -> Data -> Data -> () inline at [|| mkValidator ||]
-- {-# INLINABLE mkValidator #-} helps us to add the code to [|| mkValidator ||] because [|| mkValidator ||] requires all the code in between [|| ***** ||] to be inline 

{- 
What is a Validator
A Validator is a script that takes 3 pieces of inputs
Datum :-
Redeemer :-
Context :-

All three pieces at their lowest level are represented by the Data Datatype
 -}
mkValidator :: Data -> Data -> Data -> () -- Data to Data to Data to Unit
-- Haskell function that takes 3 arguments(All of type data) with a result type of unit 
-- This function can only return unit or an error 
-- If this function  returns unit at the end the validation will succeed
-- if there is an error during execute this function will fail

{- the simplest validator -}

mkValidator _ _ _ = traceError "NO WAY!" -- this example ignores all three arguments and returns unit as the result :: this validation will always fail but will trace the error
-- this validator script doesn't care about the 3 arguments and will always succeed
-- first argument is the datum
-- the second argument is the redeemer 
-- the third argument is the context 
-- the result is unit
-- any arbitrary transaction can consume this the UTXO that sits at this script address

{- *************************************************************************************** -}

{- mkValidator :: Data -> Data -> Data -> ()  -}
{- mkValidator _ _ _ = () -}
-- is just a haskell function and not a plutus script
-- in order to turn this haskell function into a plutus script we need to compile it with some additional code

-- creating plutus validator

validator :: Validator -- Calling validator with the results of Validator Capital letter V
validator = mkValidatorScript  $$(PlutusTx.compile [|| mkValidator ||]) 
-- Templete haskell will run on/at compiled time on [| mkValidator from above |] <- Argument
-- compile is just a template haskell function
-- The result of compile is plutus script 
-- $$() :: splice code at PlutusTx <- Add code here
-- mkValidatorScript takes:: CompiledCode (Data -> Data -> Data -> ()) -> Validator
-- [|| Turns mkValidator into the source code that defines this (Data -> Data -> Data -> ())  ||]

{- 
We still need the values of two other related types 
-- Validator Hash
-- Address
-}
-- Validator Hash and Address is easy to define once we have or Validator

{- Validator Hash -}
valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash validator

{- Address -}
-- ValidatorHash (valHash) gets turned into an address
scrAddress :: Ledger.Address
scrAddress = ScriptAddress valHash 
{- We now have an address -}

-- valHash and scrAddress returns 67129f0ae65aa04bf99ebe459d9a36d1ea3ad1cafc2f9d4a1ef2da8891007afb (my address)

{- Most code written above is boilerplate -}

{- We use the Schema to add the endpoints-}
type GiftSchema = -- this schema uses 2 endpoint named give and grab
    BlockchainActions
        .\/ Endpoint "give" Integer -- give takes an Integer argument
        {- The idea here is, if someone deposits money(ADA Lovelace) to this script address he will use the 'give' endpoint above to specify the amount-}
        .\/ Endpoint "grab" () -- grab doens't take any argument
        {- The grab endpoint looks for UTXOs at this script address to consume it -}



give :: (HasBlockchainActions s, AsContractError e) => Integer -> Contract w s e ()
give amount = do
    {- amount is just an integer, a number -}
    let tx = mustPayToOtherScript valHash (Datum $ Constr 0 []) $ Ada.lovelaceValueOf amount -- specifies the amount of Ada Lovelace to give to the script address
    {- give take the integer argument and uses the helper function  mustPayToOtherScript where we give the valHash then it takes the Datum(Which is ignored at mkValidator _ _ _ = ()  above)-}
    -- (Datum $ Constr 0 []) uses the datum constructor to turn Data into Datum :: 0 empty list
    -- we use the lovelaceValueOf helper function to turn amount into a usable value
    ledgerTx <- submitTx tx -- Submits the transaction
    void $ awaitTxConfirmed $ txId ledgerTx -- Waits until it is confirmed 
    logInfo @String $ printf "made a gift of %d lovelace" amount -- prints a log message

grab :: forall w s e. (HasBlockchainActions s, AsContractError e) => Contract w s e ()
grab = do
    utxos <- utxoAt scrAddress -- search for utxos sitting at scrAddress 67129f0ae65aa04bf99ebe459d9a36d1ea3ad1cafc2f9d4a1ef2da8891007afb
    let orefs   = fst <$> Map.toList utxos
        lookups = Constraints.unspentOutputs utxos      <> {- lookups gives the uxtos -}
                  Constraints.otherScript validator {- gives the validator -}
        tx :: TxConstraints Void Void
        tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ I 17 | oref <- orefs] {- We add a redeemer but it is ignored in this example -}
        {-  tx defined the transaction by telling it to spend script output at scrAddress 67129f0ae65aa04bf99ebe459d9a36d1ea3ad1cafc2f9d4a1ef2da8891007afb using helper function mustSpendScriptOutput-}
        -- For each UTXO that is found at utxos <- utxoAt scrAddress on line 125 we want one input where this script output is consume
        -- oref is UTXO reference
        -- this will construct a transaction that has as inputs all the UTXOs sitting at the script address scrAddress
    ledgerTx <- submitTxConstraintsWith @Void lookups tx -- looks for UTXOs to consumes
    void $ awaitTxConfirmed $ txId ledgerTx -- waits until is confirmed
    logInfo @String $ "collected gifts" -- prints a log message

endpoints :: Contract () GiftSchema Text ()
endpoints = (give' `select` grab') >> endpoints -- defines the endpoints saying that each wallet should have the option between 'give' and 'grab'
  where
    give' = endpoint @"give" >>= give
    grab' = endpoint @"grab" >>  grab

mkSchemaDefinitions ''GiftSchema

mkKnownCurrencies []
{- mkSchemaDefinitions ''GiftSchema and mkKnownCurrencies [] is just for the playground that this will be recognize-}
