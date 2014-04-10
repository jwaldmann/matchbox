module CO4.Test.TermComp2014.Standalone
where

import Prelude hiding (lex,lookup,length)
import CO4.PreludeNat
import CO4.PreludeBool (xor2)

type Map k v                   = [(k,v)]

data Pattern p                 = Any
                               | Exactly p
                               deriving (Eq,Show)

type Symbol                    = [Bool]

type Domain                    = Nat

type Label                     = [Domain]

data Term var node label       = Var  var
                               | Node node label [Term var node label]
                               deriving (Eq,Show)

data Rule var node label       = Rule (Term var node label) (Term var node label)
                               deriving (Eq,Show)

data Trs var node label        = Trs [Rule var node label]
                               deriving (Eq,Show)

data GroupedTrs var node label = GroupedTrs [[Rule var node label]]
                               deriving (Eq,Show)

type UnlabeledTerm             = Term Symbol Symbol ()
type UnlabeledRule             = Rule Symbol Symbol ()
type UnlabeledTrs              = Trs  Symbol Symbol ()

type MarkedSymbol              = (Symbol, Bool)

type DPTerm       label        = Term Symbol MarkedSymbol label
type DPRule       label        = Rule Symbol MarkedSymbol label
type DPTrs        label        = Trs  Symbol MarkedSymbol label
type GroupedDPTrs label        = GroupedTrs Symbol MarkedSymbol label

type Interpretation            = Map [Pattern Domain] Domain

type Model sym                 = Map sym Interpretation

type Sigma sym                 = Map sym Domain

type Assignments sym           = [Sigma sym]

data Order                     = Gr | Eq | NGe
                               deriving (Eq,Show)

type Precedence key            = Map key Nat

data Index                     = This | Next Index
    deriving (Eq, Show)

type ArgFilter key             = Map key [Index]

type Variable = Symbol

-- data LinearFunction = LinearFunction Nat [Nat] 

-- restricted linear functions (linear coefficients are zero or one)
data LinearFunction = LinearFunction Nat [Bool] 
    deriving (Eq, Show)

type LinearInterpretation key = Map key LinearFunction


data TerminationOrder key         = FilterAndPrec (ArgFilter key) (Precedence key)
                                  | LinearInt (LinearInterpretation key)
    deriving (Eq, Show)

type MSL = (MarkedSymbol,Label) 

constraint :: (DPTrs (), Assignments Symbol) 
           -> (Model MarkedSymbol, [ TerminationOrder MSL]) 
           -> Bool
constraint (trs,assignments) (model, orders) = 
  case makeLabeledTrs model trs assignments of
    (labeledTrs, isModel) ->
      and [ isModel
          , allRulesDecreasing         labeledTrs orders
          , existsStrongDecreasingRule labeledTrs orders
          ]

-- * make labeled TRS & search model

makeLabeledTrs :: Model MarkedSymbol -> DPTrs () -> Assignments Symbol -> (GroupedDPTrs Label, Bool)
makeLabeledTrs model (Trs rules) assignments = 
  case unzip (map (\r -> makeLabeledRule model r assignments) rules) of
    (rules', equalities) -> (GroupedTrs rules', and equalities)

makeLabeledRule :: Model MarkedSymbol -> DPRule () -> Assignments Symbol -> ([DPRule Label], Bool)
makeLabeledRule model (Rule lhs rhs) assignments = 
  let goRule sigma = case makeLabeledTerm model lhs sigma of
        (lhs', lhsValue) -> case makeLabeledTerm model rhs sigma of
          (rhs', rhsValue) -> (Rule lhs' rhs', eqValue lhsValue rhsValue)
  in
    case unzip (map goRule assignments) of
      (rules', equalities) -> (rules', and equalities)

makeLabeledTerm :: Model MarkedSymbol -> DPTerm () -> Sigma Symbol -> (DPTerm Label, Domain)
makeLabeledTerm model term sigma = case term of
  Var s         -> (Var s, valueOfVar s sigma)
  Node s _ args -> case unzip (map (\a -> makeLabeledTerm model a sigma) args) of
    (args', argsValues) -> (Node s argsValues args', valueOfFun s argsValues model)

valueOfTerm :: Model MarkedSymbol -> Sigma Symbol -> DPTerm () -> Domain
valueOfTerm model sigma term = case term of
  Var v           -> valueOfVar v sigma
  Node sym l args -> case l of 
    () -> let values = map (valueOfTerm model sigma) args
          in
            valueOfFun sym values model

valueOfFun :: MarkedSymbol -> [Domain] -> Model MarkedSymbol -> Domain
valueOfFun s args model = 
  let interp     = interpretation s model
      argPattern = map Exactly args
  in
    lookup (\xs ys -> and (zipWith (eqPattern eqValue) xs ys)) argPattern interp

valueOfVar :: Symbol -> Sigma Symbol -> Domain
valueOfVar = lookup eqSymbol

interpretation :: MarkedSymbol -> Model MarkedSymbol -> Interpretation
interpretation = lookup eqMarkedSymbol

-- * filter arguments

filterArgumentsDPTrs :: ArgFilter MSL -> DPTrs Label -> DPTrs Label
filterArgumentsDPTrs filter (Trs rules) = 
  let goRule (Rule lhs rhs) = Rule (filterArgumentsDPTerm filter lhs) 
                                   (filterArgumentsDPTerm filter rhs)
  in
    Trs (map goRule rules)

filterArgumentsDPTerm :: ArgFilter MSL -> DPTerm Label -> DPTerm Label
filterArgumentsDPTerm filter term = case term of
  Var v         -> Var v
  Node s l args -> 
    let indices = lookup eqMarkedLabeledSymbol (s,l) filter
    in
      Node s l (map (\i -> filterArgumentsDPTerm filter (atIndex i args)) indices)

-- * search precedence

allRulesDecreasing :: GroupedDPTrs Label -> [TerminationOrder MSL] -> Bool
allRulesDecreasing (GroupedTrs rules) orders =
  forall rules (all (isDecreasingRule orders))

isDecreasingRule :: [TerminationOrder MSL] -> DPRule Label -> Bool
isDecreasingRule orders (Rule lhs rhs) = 
  forall orders (\ o -> 
   let cmp = case o of
         LinearInt int -> linearRule int (Rule lhs rhs) 
         FilterAndPrec f p ->
             lpo p (filterArgumentsDPTerm f lhs) (filterArgumentsDPTerm f rhs) 
   in case cmp of
      Gr  -> True
      Eq  -> True
      NGe -> False
  )

existsStrongDecreasingRule :: GroupedDPTrs Label -> [TerminationOrder MSL] -> Bool
existsStrongDecreasingRule (GroupedTrs rules) orders =
  exists rules (all (isMarkedStrongDecreasingRule orders))

isMarkedStrongDecreasingRule :: [TerminationOrder MSL] -> DPRule Label -> Bool
isMarkedStrongDecreasingRule orders (Rule lhs rhs) = 
  exists orders (\ o -> case o of
   LinearInt int ->
       (isMarked lhs)
    && (eqOrder (linearRule int (Rule lhs rhs)) Gr)
   FilterAndPrec f p ->
       (isMarked lhs) 
    && (eqOrder (lpo p (filterArgumentsDPTerm f lhs) 
                       (filterArgumentsDPTerm f rhs)) Gr)
  )

isMarked :: DPTerm label -> Bool
isMarked term = case term of 
  Var _          -> False
  Node (_,m) _ _ -> m

-- * order from linear interpretation
-- FIXME: at the moment, this handles only unary functions (enough for SRS)
-- FIXME: bit width (3) is hardwired (in linearTerm below)

linearRule :: LinearInterpretation MSL -> DPRule Label -> Order
linearRule int (Rule lhs rhs) = 
    case linearTerm int lhs of
        LinearFunction labs llins -> 
            case linearTerm int rhs of
                LinearFunction rabs rlins -> 
                    case geNat labs rabs && and ( zipWith geBool llins rlins) of
                        False -> NGe
                        True  -> 
                            -- FIXME: co4 should translate "if" to "case" 
                            -- if gtNat labs rabs then Gr else Eq
                            case gtNat labs rabs of
                                True -> Gr ; False -> Eq

-- FIXME: this should be in CO4.Prelude, 
-- for consistency with CO4.PreludeNat.geNat ?
geBool x y = x || not y

linearTerm :: LinearInterpretation MSL -> DPTerm Label -> LinearFunction
linearTerm int t = case t of
    Var x ->  LinearFunction (nat 5 0) [ True ] 
    Node f lf args -> 
        let int_f = lookup eqMarkedLabeledSymbol (f, lf) int
            values = map ( linearTerm int ) args
        in  substitute int_f values

substitute :: LinearFunction -> [ LinearFunction ] -> LinearFunction
substitute f gs = case f of 
    LinearFunction fabs flins -> 
       let flin = head flins 
       in case gs of
           [] -> undefined
           g : rest -> case g of
                   LinearFunction gabs glins -> 
                    let glin = head glins 
                    in  LinearFunction (plusNat fabs (timesBoolNat flin gabs)) 
                                       [ flin && glin ]


timesBoolNat b n = case b of
    False -> nat 5 0 -- FIXME bitwidth
    True  -> n

-- * path orders

lpo :: Precedence MSL -> DPTerm Label -> DPTerm Label -> Order
lpo precedence s t = case t of
  Var x -> case eqLabeledDPTerm s t of 
    False -> case varOccurs x s of
                False -> NGe
                True  -> Gr
    True  -> Eq

  Node g lg ts  -> case s of
    Var _     -> NGe
    Node f lf ss -> 
      case all (\si -> eqOrder (lpo precedence si t) NGe) ss of
        False -> Gr
        True  -> case ord precedence (f,lf) (g,lg) of
                    Gr  -> case all (\ti -> eqOrder (lpo precedence s ti) Gr) ts of
                             False -> NGe
                             True  -> Gr
                    Eq  -> case all (\ti -> eqOrder (lpo precedence s ti) Gr) ts of
                             False -> NGe
                             True  -> lex (lpo precedence) ss ts
                    NGe -> NGe

ord :: Precedence MSL -> MSL -> MSL -> Order
ord prec a b = 
  let pa = lookup eqMarkedLabeledSymbol a prec
      pb = lookup eqMarkedLabeledSymbol b prec
  in
    ordNat pa pb

ordNat :: Nat -> Nat -> Order
ordNat a b = case eqNat a b of
  True  -> Eq
  False -> case gtNat a b of
    True  -> Gr
    False -> NGe

varOccurs :: Symbol -> Term Symbol node label -> Bool
varOccurs var term = case term of
  Var var'    -> eqSymbol var var'
  Node _ _ ts -> any (varOccurs var) ts

lex :: (a -> b -> Order) -> [a] -> [b] -> Order
lex ord xs ys = case xs of
  [] -> case ys of [] -> Eq
                   _  -> NGe
  x:xs' -> case ys of 
    []    -> Gr
    y:ys' -> case ord x y of 
      Gr  -> Gr
      Eq  -> lex ord xs' ys'
      NGe -> NGe

-- * utilities

atIndex :: Index -> [a] -> a
atIndex index xs = case index of
  This      -> head xs
  Next next -> atIndex next (tail xs)

lookup :: (k -> k -> Bool) -> k -> Map k v -> v
lookup f k map = case map of
  []   -> undefined
  m:ms -> case m of 
    (k',v) -> case f k k' of
      False -> lookup f k ms
      True  -> v

eqMarkedLabeledSymbol :: MSL -> MSL -> Bool
eqMarkedLabeledSymbol (s,l) (s',l') = (eqMarkedSymbol s s') && (eqLabel l l')

eqLabeledDPTerm :: DPTerm Label -> DPTerm Label -> Bool
eqLabeledDPTerm = eqTerm eqSymbol eqMarkedSymbol eqLabel

eqTerm :: (v -> v -> Bool) -> (n -> n -> Bool) -> (l -> l -> Bool) 
       -> Term v n l -> Term v n l -> Bool
eqTerm f_var f_node f_label x y = case x of
  Var u     -> case y of { Var v -> f_var u v; _ -> False }
  Node u lu us -> case y of
    Node v lv vs -> and [ f_node u v
                        , f_label lu lv
                        , eqList (eqTerm f_var f_node f_label) us vs ]
    _            -> False

eqLabel :: Label -> Label -> Bool
eqLabel = eqList eqValue

eqOrder :: Order -> Order -> Bool
eqOrder x y = case x of
  Gr  -> case y of { Gr  -> True; _ -> False }
  Eq  -> case y of { Eq  -> True; _ -> False }
  NGe -> case y of { NGe -> True; _ -> False }

eqMarkedSymbol :: MarkedSymbol -> MarkedSymbol -> Bool
eqMarkedSymbol (sym,m) (sym',m') = (eqSymbol sym sym') && (eqBool m m')

eqSymbol :: Symbol -> Symbol -> Bool
eqSymbol = eqList eqBool

eqValue :: Domain -> Domain -> Bool
eqValue = eqNat

eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqList f xs ys = case xs of
  []   -> case ys of []   -> True
                     _    -> False
  u:us -> case ys of []   -> False
                     v:vs -> (f u v) && (eqList f us vs)

eqBool :: Bool -> Bool -> Bool
eqBool x y = not (xor2 x y)

eqPattern :: (k -> k -> Bool) -> Pattern k -> Pattern k -> Bool
eqPattern f x y = case x of
  Any        -> True
  Exactly x' -> case y of
    Any        -> True
    Exactly y' -> f x' y'

exists :: [a] -> (a -> Bool) -> Bool
exists xs f = any f xs

forall :: [a] -> (a -> Bool) -> Bool
forall xs f = all f xs
