module CO4.Test.TermComp2014.Allocators
where

import           Control.Exception (assert)
import qualified Data.Map as M
import           CO4.AllocatorData (Allocator,constructors,known)
import           CO4.Prelude (kList,uList,kList',kBool,kTuple2)
import           CO4.PreludeNat (nat,kNat',uNat)
import           CO4.Util (bitWidth)
import           CO4.Test.TermComp2014.Standalone (Symbol,Domain,Trs(..),DPTrs(..),MarkedSymbol,Label)
import           CO4.Test.TermComp2014.Util (nodeArities,dpToTrs)

allocator :: Int -> Int -> Int -> DPTrs () -> Allocator
allocator bitWidth numPrecedences numPatterns dpTrs = 
  kTuple2 (modelAllocator bitWidth numPatterns trs)
          (kList numPrecedences $ kTuple2 (filterAllocator trs)
                                          (precedenceAllocator bitWidth trs))
  where
    trs = dpToTrs dpTrs

filterAllocator :: Trs v MarkedSymbol () -> Allocator
filterAllocator = kList' . map goArity . M.toList . nodeArities
  where
    goArity (s,arity) = kTuple2 (kMarkedSymbolAllocator s) (uList arity $ goIndex $ arity - 1)
    goIndex 0         = known 0 2 [ ]
    goIndex i         = constructors [ Just [], Just [ goIndex $ i - 1 ] ]

modelAllocator :: Int -> Int -> Trs v MarkedSymbol () -> Allocator
modelAllocator n numPatterns = kList' . map goArity . M.toList . nodeArities
  where
    goArity (s,arity)      = kTuple2 (kMarkedSymbolAllocator s) (goInterpretation arity)

    goInterpretation arity = if numPatterns <= 0 || numPatterns >= interpretationSize
                             then completeInterpretation
                             else incompleteInterpretation
      where
        domainSize         = 2^n
        interpretationSize = domainSize ^ arity

        completeInterpretation = kList' $ do args <- sequence $ replicate arity [0..domainSize - 1]
                                             return $ goMapping args
          where 
            goMapping args = 
              kTuple2 (kList' $ map (kPattern . Just . kValueAllocator . nat n . fromIntegral) args)
                      (uValueAllocator n)

        incompleteInterpretation = kList numPatterns goMapping
          where
            goMapping = kTuple2 (kList arity $ uPattern $ uValueAllocator n)
                                (uValueAllocator n)

uPattern :: Allocator -> Allocator
uPattern k = constructors [ Just [], Just [k] ]

kPattern :: Maybe Allocator -> Allocator
kPattern alloc = case alloc of
  Nothing -> known 0 2 []
  Just a  -> known 1 2 [ a ]

precedenceAllocator :: Int -> Trs v MarkedSymbol () -> Allocator
precedenceAllocator n trs = kList' $ concatMap goArity $ M.toList arities
  where
    arities                = nodeArities trs
    labels                 = map (nat n) [0..(2^n)-1]
    numLabeledSymbols      = (M.size arities) * (length labels)
    goArity (symbol,arity) = do
      args <- sequence $ replicate arity labels
      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
                       (uNat $ bitWidth numLabeledSymbols)

kValueAllocator :: Domain -> Allocator
kValueAllocator = kNat'
  
uValueAllocator :: Int -> Allocator
uValueAllocator = uNat

kSymbolAllocator :: Symbol -> Allocator
kSymbolAllocator s = assert (not $ null s) $ kList' $ map kBool s

kMarkedSymbolAllocator :: MarkedSymbol -> Allocator
kMarkedSymbolAllocator (s,m) = kTuple2 (kSymbolAllocator s) (kBool m)

kLabelAllocator :: Label -> Allocator
kLabelAllocator = kList' . map kValueAllocator

uLabelAllocator :: Int -> Int -> Allocator
uLabelAllocator n numArgs = kList numArgs $ uValueAllocator n
