module CO4.Test.SLPO where

import CO4.Prelude
import CO4.PreludeNat

-- * string rewriting:

type Symbol =  [ Bool ]
type Word = [ Symbol ]

data Mode = Strict | Weak deriving ( Eq, Show )
data Rule = Rule Mode Word Word deriving ( Eq, Show )
mode :: Rule -> Mode ; mode (Rule m l r) = m
lhs :: Rule -> Word ; lhs (Rule m l r) = l
rhs :: Rule -> Word ; rhs (Rule m l r) = r

type SRS = [ Rule ]



-- * label, then remove, then unlabel

data Label = Label Model [ Remove ] [ Bool ]


-- | we want 
-- data Remove = Remove_LPO QP | Remove_Interpretation Interpretation
-- but see https://github.com/apunktbau/co4/issues/35

data Remove_Tag = Remove_LPO | Remove_Interpretation
    deriving ( Eq, Show )


data Direction = Original | Reversed deriving Show

data Remove = Remove Remove_Tag Direction QP Interpretation
    deriving ( Show )

tag (Remove t d qp i) = t
direction (Remove t d qp i) = d
precedence (Remove t d qp i) = qp
interpretation (Remove t d qp i) = i


-- | lex. comb. of  interpretations removes one original rule completely 
-- (that is, all its labelled versions)
constraint srs lab = case lab of
    Label mod qps remove -> 
          let result = labelled srs mod
              srss = map (map snd) result
              values = concat ( map (map fst) result )
              css  = map (map (comps qps  )) srss
          in     not ( any (any isNone) css ) -- ^ all are compatible at least weakly
              && or remove -- ^ at least one strictly
              && eqSymbol remove ( map ( all isGreater ) css ) -- ^ we guessed correctly
              && all (\(ltop,rtop) -> eqSymbol ltop rtop) values -- ^ we have a model
              && all ( \ rem -> case rem of Remove tag dir qp int -> positiveI int ) qps

-- * model, labelling

type Model = Tree Func
type Func = Tree [Bool]
    
-- | produces semantically labelled version (one SRS for each rule)
-- (the type is identical but the symbols have additional bits)
labelled :: SRS -> Model -> [ [ ((Value,Value),Rule) ] ]
labelled srs mod =
    let ks = keys ( leftmost mod )
        labelRule u k = case labelledW mod (lhs u) k of 
                ( ltop, l' ) -> case labelledW mod (rhs u) k of 
                    ( rtop, r' ) -> ((ltop,rtop),Rule (mode u) l' r')
    in  map ( \ u ->  map ( \ k -> labelRule u k ) ks    ) srs 

type Value = [Bool]

-- labelledW :: Model -> [Symbol] -> Value -> (Value,[Symbol])
labelledW mod w k = case assertKnown w of
            [] -> (k, [])
            x:xs' -> case labelledW mod xs' k of
                (k', ys) -> let s = get mod x
                            in  (get s k'
                                 , (labelledW_app x k') : ys )

labelledW_app x k' = x ++ assertKnown k'

-- | binary decision tree, used to map bitstrings to values
data Tree a = Leaf a | Branch (Tree a) (Tree a) 
     deriving Show


-- keys :: Tree a -> [[Bool]]
keys t = case t of
    Leaf _ -> [[]]
    Branch l r -> map (False :) (keys l) ++ map (True :) (keys r)

-- leftmost :: Tree a -> a
leftmost t = case t of
    Leaf x -> x
    Branch l r -> leftmost l

eqFunc s t = case s of
    Leaf x -> case t of
        Leaf y -> eqSymbol x y -- x == y
        _ -> undefined
    Branch l r -> case t of
        Leaf y -> undefined
        Branch p q -> (eqFunc l p) && (eqFunc r q)

-- | wrong way: first g, then f  (information goes from right to left)
timesF :: Tree a -> Tree [Bool] -> Tree a
timesF f g = case g of
    Leaf w -> Leaf (get f w)
    Branch l r -> Branch (timesF f l) (timesF f r)

get :: Tree a -> [Bool] -> a
get t p = case assertKnown p of 
    []   -> case assertKnown t of 
         Leaf x -> x
         Branch l r -> undefined
    x:p' -> case assertKnown t of
         Leaf x -> undefined 
         Branch l r -> 
             get (assertKnown (case x of False -> l ; True -> r)) p'
             -- case x of { False -> get l p' ; True  -> get r p' } 

-- * lex. combination

data Comp = Greater | GreaterEquals | None deriving Show

isNone c = case c of { None -> True ; _ -> False }
isGreaterEquals c = case c of { GreaterEquals -> True ; _ -> False }
isGreater c = case c of { Greater -> True ; _ -> False }



comps :: [ Remove ] -> Rule -> Comp
comps rs u = lexi (map ( \ r -> comp r u) rs )


lexi :: [Comp] -> Comp
lexi cs = case cs of
    [] -> GreaterEquals
    c : cs' -> case c of
        Greater -> Greater
        GreaterEquals -> lexi cs'
        None -> None

comp :: Remove -> Rule -> Comp
comp r u = 
    let rev u = Rule (mode u) (reverse (lhs u)) (reverse (rhs u)) 
        c u = case tag r of
            Remove_LPO -> comp_lpo (precedence r) u
            Remove_Interpretation -> comp_interpretation (interpretation r) u
    in  -- case direction r of { Original -> c u ; Reversed -> c (rev u) }
        c ( case direction r of { Original -> u ; Reversed -> (rev u) } )


-- * path order (with deletion of symbols)

comp_lpo qp u = 
    compareW (\ x -> get (delete qp) x)
             (compareS (order qp)) (lhs u) (rhs u)

data QP = 
     QP (Tree Bool) -- ^ False: delete symbol
        (Tree Nat) -- ^  height in the precedence
    deriving Show

delete (QP del ord) = del
order  (QP del ord) = ord

type Preorder s = s -> s -> Comp

compareS :: Tree Nat -> Preorder Symbol
compareS t x y = 
    let qx = get t x ; qy = get t y
    in  case eqNat qx qy of
            True -> GreaterEquals
            False -> case gtNat qx qy of
                 True -> Greater
                 False -> None

type Delete s = s -> Bool

-- | this relies on memoization (else, it is inefficient)

lpoGT :: Delete s -> Preorder s -> [s] -> [s] -> Bool
lpoGT del comp xs ys = case xs of
    [] -> False
    x : xs' -> case del x of
       True -> lpoGT del comp xs' ys
       False -> lpoGE del comp xs' ys || case ys of
          [] -> True
          y : ys' -> case del y of
              True -> lpoGT del comp (x:xs') ys'
              False -> lpoGT del comp xs ys' && case comp x y of
                  Greater -> True
                  GreaterEquals -> lpoGT del comp xs' ys' 
                  None -> False

lpoGE :: Delete s -> Preorder s -> [s] -> [s] -> Bool
lpoGE del comp xs ys = lpoEQ del comp xs ys || lpoGT del comp xs ys

lpoEQ :: Delete s -> Preorder s -> [s] -> [s] -> Bool
lpoEQ del comp xs ys = case xs of
    [] -> case ys of
        [] -> True
        y : ys' -> case del y of
           True -> lpoEQ del comp xs ys'
           False -> False
    x : xs' -> case del x of
        True -> lpoEQ del comp xs' ys
        False -> case ys of
            [] -> False
            y : ys' -> case del y of
                True -> lpoEQ del comp (x:xs') ys'
                False -> isGreaterEquals (comp x y) 
                      && lpoEQ del comp xs' ys'

compareW :: Delete s -> Preorder s -> Preorder [s]
compareW del comp xs ys = 
    case lpoGT del comp xs ys of
        True -> Greater
        False -> case lpoGE del comp xs ys of
           True -> GreaterEquals
           False -> None

-- following hack makes eqSymbol monomorphic
-- so it can be used as argument for elemWith
eqSymbol p q = (p == q ) && case p of
    [] -> True ; x : xs -> case x of 
         True -> True ; False -> True

eqWord xs ys = case xs of
    [] -> case ys of
        [] -> True
        y : ys' -> False
    x : xs' -> case ys of
        [] -> False
        y : ys' -> eqSymbol x y && eqWord xs' ys'

-- * matrix interpretations

data Interpretation_Tag = Arctic_Tag | Natural_Tag
    deriving Show

data Interpretation 
   = Interpretation Interpretation_Tag
         (Tree (Linear Arctic))
         (Tree (Linear    Nat))
    deriving Show

comp_interpretation :: Interpretation -> Rule -> Comp
comp_interpretation i u = case i of
    Interpretation tag ai ni -> case tag of
        Natural_Tag -> case iRuleN ni u of
            (l,r) -> case geLN l r of
                False -> None
                True ->  case gtLN l r of
                    True -> Greater
                    False -> GreaterEquals
        Arctic_Tag -> case iRuleA ai u of
            (l,r) -> case geLA l r of
                False -> None
                True ->  case gtLA l r of
                    True -> Greater
                    False -> GreaterEquals

positiveI :: Interpretation -> Bool
positiveI i = case i of
    Interpretation tag ai ni -> case tag of
        Natural_Tag -> allI positiveLN ni
        Arctic_Tag  -> allI positiveLA ai

allI :: (a -> Bool) -> Tree a -> Bool
allI prop t = case t of
    Leaf x -> prop x
    Branch l r -> allI prop l && allI prop r

positiveMA :: Matrix Arctic -> Bool
positiveMA m = finite (head (head m))

positiveMN :: Matrix Nat -> Bool
positiveMN m = 
       not (isZeroNat (head (head m))) 
    && not (isZeroNat (last (last m))) 

gtMA a b = and ( zipWith ( \ xs ys -> and (zipWith ggA xs ys)  ) a b )
geMA a b = and ( zipWith ( \ xs ys -> and (zipWith geA xs ys)  ) a b )

geMN a b = and ( zipWith ( \ xs ys -> and (zipWith geNat xs ys)  ) a b )
gtMN a b = gtNat (last (head a)) (last(head b))



iSymbol i s = get i s

iWord timesL i w = case w of
    [] -> undefined
    x : xs -> let m = iSymbol i x 
              in case xs of
                    [] -> m
                    _  -> timesL m (iWord timesL i xs)

iRule timesL i u = (iWord timesL i (lhs u), iWord timesL i (rhs u))

iRuleA i u = iRule (timesL   plusA   timesA) i u
iRuleN i u = iRule (timesL plusNat timesNat) i u


-- * linear (vector values) functions

data Linear a = Linear ( Matrix a ) -- ^ factor 
                       ( Matrix a ) -- ^ absolute part (as column vector)
   deriving Show

plusL plus f g = case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> Linear (plusM plus f1 g1) (plusM plus f0 g0)

timesL plus times f g = case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> Linear (timesM plus times f1 g1) 
                               (plusM plus f0 (timesM plus times f1 g0))

positiveLA f = case f of
    Linear f1 f0 -> positiveMA f1 

positiveLN f = case f of
    Linear f1 f0 -> not (isZeroNat (head (head f1))) 

geLN f g =  case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> geMN f1 g1 && geMN f0 g0

geLA f g =  case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> geMA f1 g1 && geMA f0 g0

gtLN f g =  case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> gtMN f0 g0

gtLA f g =  case f of 
    Linear f1 f0 -> case g of
        Linear g1 g0 -> gtMA f1 g1 && gtMA f0 g0


-- * matrices:

type Matrix a = [[a]]


plusM plus a b = zipWith (zipWith plus) a b

timesM plus times a b = 
    let b' = transpose b
    in  map ( \ row -> map ( dot plus times row ) b' ) a

transpose xss = case xss of
    [] -> []
    xs : xss' -> case xss' of
        [] -> map (\ x -> [x]) xs
        _  -> zipWith (:) xs ( transpose xss')

dot plus times xs ys = 
    let sum xs = foldr plus (head xs) (tail xs)
    in  sum ( zipWith times xs ys)

-- * arctic operations:

data Arctic = MinusInfinity | Finite Nat
    deriving (Eq, Show)

infinite a = case a of
    MinusInfinity -> True
    _ -> False

finite a = case a of
    MinusInfinity -> False
    _ -> True

ggA a b = gtA a b || infinite b 

gtA a b = not (geA b a)

geA a b = case b of
  MinusInfinity -> True
  Finite b' -> case a of 
    MinusInfinity -> False
    Finite a' -> geNat a' b'

plusA :: Arctic -> Arctic -> Arctic
plusA e f = case e of
  MinusInfinity -> f
  Finite x -> Finite ( case f of 
    MinusInfinity -> x 
    Finite y      -> maxNat x y  )

timesA :: Arctic -> Arctic -> Arctic
timesA e f = case e of
  MinusInfinity -> MinusInfinity
  Finite x -> case f of 
    MinusInfinity -> MinusInfinity
    Finite y      -> Finite (plusNat x y)






