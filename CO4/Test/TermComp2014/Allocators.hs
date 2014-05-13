module CO4.Test.TermComp2014.Allocators
where

import qualified Data.Map as M
import           CO4.Allocator.Data (Allocator,constructors,known)
import           CO4.Prelude (kList,uList,kList',kBool,uBool,kTuple2)
import           CO4.PreludeNat (nat,kNat',uNat)
import           CO4.Util (bitWidth)
import           CO4.Test.TermComp2014.Standalone (Symbol,Domain,DPTrs,Label,Model,UsableOrder,MSL,Proof)
import           CO4.Test.TermComp2014.Util (nodeArities)
import           CO4.Test.TermComp2014.Config

type Talloc t = Allocator -- with phantom type


-- type UsableOrder key =  (UsableSymbol key, TerminationOrder key)

-- data Proof = Proof (Model MarkedSymbol) [UsableOrder MSL]

aProof :: Talloc (Model Symbol) -> Talloc [UsableOrder MSL] -> Talloc Proof
aProof mod orders = known 0 1 [ mod, orders ]

aTuple2 :: Talloc a -> Talloc b -> Talloc (a,b)
aTuple2 a1 a2 = known 0 1 [ a1, a2 ]

aList :: Int -> Talloc a -> Talloc [a]
aList k a = kList k a

allocator :: Config -> DPTrs () -> Talloc Proof
allocator config dpTrs = 
  aProof (modelAllocator config dpTrs)
          (aList (numPrecedences config) $ usableOrderAllocator config dpTrs )
{-
         $ kList' 
         $  [ known 0 2 [ filterAllocator config dpTrs, precedenceAllocator config dpTrs ]
            | usePrecedence config ]
         ++ [ known 1 2 [ interpretationAllocator config dpTrs ]
            | useInterpretation config ]
-}

usableOrderAllocator :: Config -> DPTrs () -> Allocator
usableOrderAllocator config dpTrs =
    known 0 1 [ usableMapAllocator config dpTrs
              , orderAllocator config dpTrs
              ]

usableMapAllocator :: Config -> DPTrs () -> Allocator
usableMapAllocator config = kList' . concatMap goArity . M.toList . nodeArities
  where
    n                 = modelBitWidth config
    height            = 2^n
    labels            = map (nat n) [0..height-1]
    goArity (s,arity) = do
      args <- sequence $ replicate arity labels
      return $ kTuple2 (kTuple2 (kSymbolAllocator s) (kLabelAllocator args))
             $ uBool

orderAllocator :: Config -> DPTrs () -> Allocator
orderAllocator config dpTrs = 
    case (usePrecedence config, useInterpretation config) of
        (True,False) -> 
             known 0 2 [ filterAllocator config dpTrs, precedenceAllocator config dpTrs ]
        (False,True) -> 
             known 1 2 [ interpretationAllocator config dpTrs ]
        (True,True) -> 
             error "FIXME: have the solver choose the order type"

filterAllocator :: Config -> DPTrs () -> Allocator
filterAllocator config = kList' . concatMap goArity . M.toList . nodeArities
  where
    n                 = modelBitWidth config
    height            = 2^n
    labels            = map (nat n) [0..height-1]
    goArity (s,arity) = do
      args <- sequence $ replicate arity labels
      let selection = 
            case argumentFilter config of
              AFBrute  -> kList' []
              AFNormal -> uList arity $ uIndex $ arity - 1

          projection = uIndex $ arity - 1

      return $ kTuple2 (kTuple2 (kSymbolAllocator s) (kLabelAllocator args))
             $ case (arity, argumentFilter config) of
                (0, _)      -> known 0 2 [ kList' [] ]
                (a, AFNone) -> known 0 2 [ kList' $ map kIndex [0 .. a-1] ]
                (_, _)      -> constructors [ Just [selection] , Just [projection] ]

    uIndex i | i < 0 = error "TermComp2014.Allocators.filterAllocator.uIndex"
    uIndex 0         = known 0 2 [ ]
    uIndex i         = constructors [ Just [], Just [ uIndex $ i - 1 ] ]

    kIndex i | i < 0 = error "TermComp2014.Allocators.filterAllocator.kIndex"
    kIndex 0         = known 0 2 [ ]
    kIndex i         = known 1 2 [ kIndex $ i - 1 ]

interpretationAllocator :: Config -> DPTrs () -> Allocator
interpretationAllocator config trs = kList' $ concatMap goArity arities
  where
    arities                = M.toList $ nodeArities trs
    n                      = modelBitWidth config
    height                 = 2^n
    labels                 = map (nat n) [0..height-1]
    absoluteCoefficientBitWidth    = 3 -- FIXME make configurable
    -- NOTE: this bit width is also hardwired in Standalone.hs (function linearTerm)
    linfun ar = known 0 1 [ uNat absoluteCoefficientBitWidth
                          , kList' $ replicate ar uBool
                          ]

    goArity (symbol,arity) = do
      args <- sequence $ replicate arity labels
      return $ kTuple2 (kTuple2 (kSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
             $ linfun arity


modelAllocator :: Config -> DPTrs () -> Allocator
modelAllocator config = kList' . map goArity . M.toList . nodeArities
  where
    {-
    goArity (sym@(_,marked),arity) = kTuple2 (kSymbolAllocator sym) $
      if marked 
      then kList' [ kTuple2 (kList' [kPattern Nothing]) (kValueAllocator $ nat 0 0) ]
      else goInterpretation arity
      -}
    goArity (sym,arity) = kTuple2 (kSymbolAllocator sym) $ goInterpretation arity

    goInterpretation arity = if (numPatterns config) <= 0 || 
                                (numPatterns config) >= interpretationSize
                             then completeInterpretation
                             else incompleteInterpretation
      where
        domainSize         = 2^(modelBitWidth config)
        interpretationSize = domainSize ^ arity

        completeInterpretation = kList' $ do args <- sequence $ replicate arity [0..domainSize - 1]
                                             return $ goMapping args
          where 
            goMapping args = 
              kTuple2 (kList' $ map (kPattern . Just . kValueAllocator 
                                              . nat (modelBitWidth config) 
                                              . fromIntegral) args)
                      (uValueAllocator $ modelBitWidth config)

        incompleteInterpretation = kList (numPatterns config) goMapping
          where
            goMapping = kTuple2 (kList arity $ uPattern $ uValueAllocator $ modelBitWidth config)
                                (uValueAllocator $ modelBitWidth config)

uPattern :: Allocator -> Allocator
uPattern k = constructors [ Just [], Just [k] ]

kPattern :: Maybe Allocator -> Allocator
kPattern alloc = case alloc of
  Nothing -> known 0 2 []
  Just a  -> known 1 2 [ a ]

precedenceAllocator :: Config -> DPTrs () -> Allocator
precedenceAllocator config trs = 
    if emptyPrecedence config 
    then known 0 2 []
    else known 1 2 [ kList' $ concatMap goArity arities ]
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
      return $ kTuple2 (kTuple2 (kSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
                       (uNat precedenceBitWidth)

kValueAllocator :: Domain -> Allocator
kValueAllocator = kNat'
  
uValueAllocator :: Int -> Allocator
uValueAllocator = uNat

kSymbolAllocator :: Symbol -> Allocator
kSymbolAllocator = kNat'

kLabelAllocator :: Label -> Allocator
kLabelAllocator = kList' . map kValueAllocator

uLabelAllocator :: Int -> Int -> Allocator
uLabelAllocator n numArgs = kList numArgs $ uValueAllocator n
