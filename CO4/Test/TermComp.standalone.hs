module TermComp where

type Symbol   = [Bool]
type Variable = [Bool]

data Term = Var Variable
          | Term Symbol [ Term ] -- deriving Eq

data Order = Gr | Eq | NGe -- deriving Eq

type Precedence = [Symbol]

type TRS = [(Term,Term)]

main trs prec = 
  (isPrec prec) 
   &&  (all (\rule -> case rule of
         (lhs, rhs) -> (lpo (ord prec) lhs rhs) == Gr )
                      trs
       )

-- following hack makes eqSymbol monomorphic
-- so it can be used as argument for elemWith
eqSymbol p q = (p == q ) && case p of
    [] -> True ; x : xs -> case x of 
         True -> True ; False -> True
    

isPrec prec = case prec of
  [] -> True
  p : ps ->  (not (elemWith eqSymbol p ps))
             &&       (isPrec ps)

lpo :: (Symbol -> Symbol -> Order) 
    -> Term -> Term -> Order
lpo ord s t = case t of
  Var x     -> case s == t of 
                  False -> case occurs x s of
                              False -> NGe
                              True  -> Gr
                  True  -> Eq
  Term g ts  -> case s of
    Var _     -> NGe
    Term f ss -> 
      case all (\si -> (lpo ord si t) == NGe) ss of
        False -> Gr
        True  -> case ord f g of
                    Gr  -> case all (\ti -> (lpo ord s ti) == Gr) ts of
                             False -> NGe
                             True  -> Gr
                    Eq  -> case all (\ti -> (lpo ord s ti) == Gr) ts of
                             False -> NGe
                             True  -> lexi (lpo ord) ss ts
                    NGe -> NGe

ord :: Precedence -> Symbol -> Symbol -> Order
ord prec a b = case a == b of
  False -> case greater prec a b of
              False -> NGe
              True  -> Gr
  True  -> Eq

greater :: Precedence -> Symbol -> Symbol -> Bool
greater prec a b = case prec of
  []          -> False
  p : prec' -> ((p == a) &&
                            (elemWith eqSymbol b prec')
                      ) ||
                      (greater prec' a b)

occurs :: Variable -> Term -> Bool
occurs v term = case term of
  Var v'    -> v == v'
  Term _ ts -> any (occurs v) ts

lexi :: (a -> b -> Order) -> [a] -> [b] -> Order
lexi ord xs ys = case xs of
  [] -> case ys of 
    []      -> Eq
    _ : _ -> NGe

  x : xs' -> case ys of 
    []        -> Gr
    y : ys' -> case ord x y of 
      Gr  -> Gr
      Eq  -> lexi ord xs' ys'
      NGe -> NGe
  
elemWith :: (a -> a -> Bool) -> a -> [a] -> Bool
elemWith eq x xs = case xs of
  []       -> False
  y : ys -> (eq x y) || (elemWith eq x ys)


