{-# LANGUAGE TemplateHaskell #-}
module CO4.Test.TermComp2014.Allocators
  (allocator)
where

import qualified Data.Map as M
import           CO4 hiding (Config)
import           CO4.Prelude (kList,uList,allocatorList)
import           CO4.PreludeNat (Nat,nat,uNat,knownNat)
import           CO4.Util (bitWidth)
<<<<<<< HEAD
import           CO4.Test.TermComp2014.Standalone (Symbol,Domain,DPTrs,MarkedSymbol,Label)
import           CO4.Test.TermComp2014.Util (nodeArities)
import           CO4.Test.TermComp2014.Config

allocator :: Config -> DPTrs () -> Allocator
allocator config dpTrs = 
  kTuple2 (modelAllocator config dpTrs)
          (kList (numPrecedences config) $ orderAllocator config dpTrs )
{-
         $ kList' 
         $  [ known 0 2 [ filterAllocator config dpTrs, precedenceAllocator config dpTrs ]
            | usePrecedence config ]
         ++ [ known 1 2 [ interpretationAllocator config dpTrs ]
            | useInterpretation config ]
-}

orderAllocator :: Config -> DPTrs () -> Allocator
=======
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
>>>>>>> 017be4e... add typed allocators (issue #39)
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
<<<<<<< HEAD
      let selection = 
               if bruteFilter config
               then kList' []
               else uList arity $ goIndex $ arity - 1
          projection = goIndex $ arity - 1

      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator s) (kLabelAllocator args))
             $ case args of
                [] -> known 0 2 [ kList' [] ]
                _  -> (constructors [ Just [selection] , Just [projection] ])
                       -- known 0 2 [ selection ]

    goIndex i | i < 0 = error "TermComp2014.Allocators.filterAllocator.goIndex"
    goIndex 0         = known 0 2 [ ]
    goIndex i         = constructors [ Just [], Just [ goIndex $ i - 1 ] ]
=======
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
<<<<<<< HEAD
    kIndex i         = unsafeTAllocator $ go i
      where
        go 0 = known 0 2 [ ]
        go i = known 1 2 [ go $ i - 1 ]
>>>>>>> 017be4e... add typed allocators (issue #39)
=======
    kIndex 0         = knownThis
    kIndex i         = knownNext $ kIndex $ i - 1
>>>>>>> 5d03d8c... add union(s) of allocators (issue #93)

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
<<<<<<< HEAD
      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator symbol) 
=======
      return $ knownTuple2 (knownTuple2 (kSymbolAllocator symbol) 
>>>>>>> 017be4e... add typed allocators (issue #39)
                                (kLabelAllocator args)
                       ) 
             $ linfun arity

modelAllocator :: Config -> DPTrs () -> TAllocator (Model Symbol)
modelAllocator config = allocatorList . map goArity . M.toList . nodeArities
  where
    goArity (sym@(_,marked),arity) = kTuple2 (kMarkedSymbolAllocator sym) $
      if marked 
      then kList' [ kTuple2 (kList' [kPattern Nothing]) (kValueAllocator $ nat 0 0) ]
      else goInterpretation arity
<<<<<<< HEAD
=======
      -}
    goArity (sym,arity) = knownTuple2 (kSymbolAllocator sym) $ goInterpretation arity
>>>>>>> 017be4e... add typed allocators (issue #39)

    goInterpretation arity = if (numPatterns config) <= 0 || 
                                (numPatterns config) >= interpretationSize
                             then completeInterpretation
                             else incompleteInterpretation
      where
        domainSize         = 2^(modelBitWidth config)
        interpretationSize = domainSize ^ arity

        completeInterpretation = allocatorList $ do 
          args <- sequence $ replicate arity [0..domainSize - 1]
          return $ goMapping args
          where 
            goMapping args = 
              knownTuple2 (allocatorList $ map (knownExactly . kValueAllocator 
                                                             . nat (modelBitWidth config) 
                                                             . fromIntegral) args)
                          (uValueAllocator $ modelBitWidth config)

        incompleteInterpretation = kList (numPatterns config) goMapping
          where
            goMapping = knownTuple2 (kList arity uPattern)
                                    (uValueAllocator $ modelBitWidth config)

            uPattern = union knownAny 
                     $ knownExactly $ uValueAllocator 
                                    $ modelBitWidth config

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
<<<<<<< HEAD
      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator symbol) 
=======
      return $ knownTuple2 (knownTuple2 (kSymbolAllocator symbol) 
>>>>>>> 017be4e... add typed allocators (issue #39)
                                (kLabelAllocator args)
                       ) 
                       (uNat precedenceBitWidth)

kValueAllocator :: Domain -> TAllocator Domain
kValueAllocator = fromKnown
  
uValueAllocator :: Int -> TAllocator Domain
uValueAllocator = uNat

<<<<<<< HEAD
kSymbolAllocator :: Symbol -> Allocator
kSymbolAllocator = kNat'

kMarkedSymbolAllocator :: MarkedSymbol -> Allocator
kMarkedSymbolAllocator (s,m) = kTuple2 (kSymbolAllocator s) (kBool m)

kLabelAllocator :: Label -> Allocator
kLabelAllocator = kList' . map kValueAllocator
=======
kSymbolAllocator :: Symbol -> TAllocator Symbol
kSymbolAllocator = fromKnown
>>>>>>> 017be4e... add typed allocators (issue #39)

kLabelAllocator :: Label -> TAllocator Label
kLabelAllocator = fromKnown
