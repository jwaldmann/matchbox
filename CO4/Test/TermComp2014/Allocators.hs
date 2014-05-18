{-# LANGUAGE TemplateHaskell #-}
module CO4.Test.TermComp2014.Allocators
  (allocator)
where

import qualified Data.Map as M
import           CO4 hiding (Config)
import           CO4.Prelude (kList,uList,allocatorList)
import           CO4.PreludeNat (Nat,nat,uNat,knownNat)
import           CO4.Util (bitWidth)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Util (nodeArities)
import           CO4.Test.TermComp2014.Config

$( compileFile [OnlyAllocators, ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

allocator :: Config -> DPTrs () -> TAllocator Proof
allocator config dpTrs = 
  knownProof (modelAllocator config dpTrs)
             (kList (numPrecedences config) $ usableOrderAllocator config dpTrs )

usableOrderAllocator :: Config -> DPTrs () -> TAllocator (UsableOrder MSL)
usableOrderAllocator config dpTrs =
    knownTuple2 (usableMapAllocator config dpTrs) (orderAllocator config dpTrs)

usableMapAllocator :: Config -> DPTrs () -> TAllocator (UsableSymbol MSL)
usableMapAllocator config = allocatorList . concatMap goArity . M.toList . nodeArities
  where
    n                 = modelBitWidth config
    height            = 2^n
    labels            = map (nat n) [0..height-1]
    goArity (s,arity) = do
      args <- sequence $ replicate arity labels
      return $ knownTuple2 (knownTuple2 (kSymbolAllocator s) (kLabelAllocator args))
                           complete

orderAllocator :: Config -> DPTrs () -> TAllocator (TerminationOrder MSL)
orderAllocator config dpTrs = 
    case (usePrecedence config, useInterpretation config) of
        (True,False) -> 
             knownFilterAndPrec (filterAllocator config dpTrs) (precedenceAllocator config dpTrs)
        (False,True) -> 
             knownLinearInt (interpretationAllocator config dpTrs)
        (True,True) -> 
             error "FIXME: have the solver choose the order type"

filterAllocator :: Config -> DPTrs () -> TAllocator (ArgFilter MSL)
filterAllocator config = allocatorList . concatMap goArity . M.toList . nodeArities
  where
    n                 = modelBitWidth config
    height            = 2^n
    labels            = map (nat n) [0..height-1]
    goArity (s,arity) = do
      args <- sequence $ replicate arity labels
      let selectionIndices = 
            case argumentFilter config of
              AFBrute  -> knownNil
              AFNormal -> uList arity $ uIndex $ arity - 1

          projectionIndex = uIndex $ arity - 1

      return $ knownTuple2 (knownTuple2 (kSymbolAllocator s) (kLabelAllocator args))
             $ case (arity, argumentFilter config) of
                (0, _)      -> knownSelection knownNil
                (a, AFNone) -> knownSelection $ allocatorList $ map kIndex [0 .. a-1]
                (_, _)      -> union (knownSelection  $ selectionIndices)
                                     (knownProjection $ projectionIndex)

    uIndex i | i < 0 = error "TermComp2014.Allocators.filterAllocator.uIndex"
    uIndex 0         = knownThis
    uIndex i         = union knownThis $ knownNext $ uIndex $ i - 1

    kIndex i | i < 0 = error "TermComp2014.Allocators.filterAllocator.kIndex"
    kIndex 0         = knownThis
    kIndex i         = knownNext $ kIndex $ i - 1

interpretationAllocator :: Config -> DPTrs () -> TAllocator (LinearInterpretation MSL)
interpretationAllocator config trs = allocatorList $ concatMap goArity arities
  where
    arities                = M.toList $ nodeArities trs
    n                      = modelBitWidth config
    height                 = 2^n
    labels                 = map (nat n) [0..height-1]
    absoluteCoefficientBitWidth    = 5 -- FIXME make configurable
    -- NOTE: this bit width is also hardwired in Standalone.hs (function linearTerm)
    linfun ar = knownLinearFunction (uNat absoluteCoefficientBitWidth)
                                    (allocatorList $ replicate ar complete)

    goArity (symbol,arity) = do
      args <- sequence $ replicate arity labels
      return $ knownTuple2 (knownTuple2 (kSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
             $ linfun arity

modelAllocator :: Config -> DPTrs () -> TAllocator (Model Symbol)
modelAllocator config = allocatorList . map goArity . M.toList . nodeArities
  where
    {-
    goArity (sym@(_,marked),arity) = kTuple2 (kSymbolAllocator sym) $
      if marked 
      then kList' [ kTuple2 (kList' [kPattern Nothing]) (kValueAllocator $ nat 0 0) ]
      else goInterpretation arity
      -}
    goArity (sym,arity) = knownTuple2 (kSymbolAllocator sym) $ goInterpretation arity

    goInterpretation arity = if (numPatterns config) <= 0 || 
                                (numPatterns config) >= interpretationSize
                             then completeInterpretation 
                             else incompleteInterpretation 
      where
        domainSize         = 2^(modelBitWidth config)
        interpretationSize = domainSize ^ arity
        uval = uValueAllocator $ modelBitWidth config
        completeInterpretation = allocatorList $ do 
          args <- sequence $ replicate arity [0..domainSize - 1]
          return $ goMapping args
          where 
            goMapping args = 
              knownTuple2 (allocatorList $ map (knownExactly . kValueAllocator 
                                                             . nat (modelBitWidth config) 
                                                             . fromIntegral) args)
                          uval

        incompleteInterpretation = allocatorList $ do
            k <- [ 1 .. numPatterns config]
            let uPattern = union knownAny $ knownExactly uval
                p = if  k < numPatterns config then uPattern else knownAny
            return $ knownTuple2 ( kList arity p)  uval 

precedenceAllocator :: Config -> DPTrs () -> TAllocator (Precedence MSL)
precedenceAllocator config trs = 
    if emptyPrecedence config 
    then knownEmptyPrecedence
    else knownPrecedence $ allocatorList $ concatMap goArity arities
  where
    arities                = M.toList $ nodeArities trs
    n                      = modelBitWidth config
    height                 = 2^n
    labels                 = map (nat n) [0..height-1]
    precedenceBitWidth     =
      if precedenceDomainBitWidth config < 0
      then bitWidth $ sum $ map (\(_,arity) -> height^arity) arities
      else precedenceDomainBitWidth config

    goArity (symbol,arity) = do
      args <- sequence $ replicate arity labels
      return $ knownTuple2 (knownTuple2 (kSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
                       (uNat precedenceBitWidth)

kValueAllocator :: Domain -> TAllocator Domain
kValueAllocator = fromKnown
  
uValueAllocator :: Int -> TAllocator Domain
uValueAllocator = uNat

kSymbolAllocator :: Symbol -> TAllocator Symbol
kSymbolAllocator = fromKnown

kLabelAllocator :: Label -> TAllocator Label
kLabelAllocator = fromKnown
