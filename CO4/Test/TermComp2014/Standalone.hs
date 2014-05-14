module CO4.Test.TermComp2014.Standalone
where

import Prelude hiding (lex,lookup,length)
import CO4.Prelude (assertKnown)
import CO4.PreludeNat
import CO4.PreludeBool (xor2)

type Map k v                   = [(k,v)]

data Pattern p                 = Any
                               | Exactly p
                               deriving (Eq,Show)

type Symbol                    = Nat

type Domain                    = Nat

type Label                     = [Domain]

data Term var node label       = Var  var
                               | Node node label [Term var node label]
                               deriving (Eq,Show)

data Rule var node label       = Rule Bool (Term var node label) (Term var node label)
                               deriving (Eq,Show)

data Trs var node label        = Trs [Rule var node label]
                               deriving (Eq,Show)

data GroupedTrs var node label = GroupedTrs [[Rule var node label]]
                               deriving (Eq,Show)


-- | the tag says whether the rule should be considered for weak compatibility.
-- A Tag is false:
-- For unmarked rules: the rule is not usable (w.r.t. to the marked rules in the input)
-- For marked rules: the rule was already removed because it was strictly compatible
-- with some earlier ordering


data TaggedGroupedTrs var node label = TaggedGroupedTrs [[(Bool,Rule var node label)]]
    deriving ( Eq, Show )



type UnlabeledTerm             = Term Symbol Symbol ()
type UnlabeledRule             = Rule Symbol Symbol ()
type UnlabeledTrs              = Trs  Symbol Symbol ()

type DPTerm       label        = Term Symbol Symbol label
type DPRule       label        = Rule Symbol Symbol label
type DPTrs        label        = Trs  Symbol Symbol label
type GroupedDPTrs label        = GroupedTrs Symbol Symbol label

type TaggedGroupedDPTrs label  = TaggedGroupedTrs Symbol Symbol label

type Interpretation            = Map [Pattern Domain] Domain

type Model sym                 = Map sym Interpretation

type Sigma sym                 = Map sym Domain

type Assignments sym           = [Sigma sym]

data Order                     = Gr | Eq | NGe
                               deriving (Eq,Show)

data Precedence key            = EmptyPrecedence
                               | Precedence (Map key Nat)
     deriving (Eq, Show )

data Index                     = This | Next Index
    deriving (Eq, Show)

data Filter = Selection [ Index ]
            | Projection Index
    deriving (Eq, Show )

type ArgFilter key             = Map key Filter

type Variable = Symbol

-- data LinearFunction = LinearFunction Nat [Nat] 

-- restricted linear functions (linear coefficients are zero or one)
data LinearFunction = LinearFunction Nat [Bool] 
    deriving (Eq, Show)

type LinearInterpretation key = Map key LinearFunction


data TerminationOrder key         = FilterAndPrec (ArgFilter key) (Precedence key)
                                  | LinearInt (LinearInterpretation key)
    deriving (Eq, Show)

type UsableSymbol key = Map key Bool

type MSL = (Symbol,Label) 


type UsableOrder key =  (UsableSymbol key, TerminationOrder key)

data Proof = Proof (Model Symbol) [UsableOrder MSL] deriving Show


constraint :: (DPTrs (), [Domain]) 
           -> Proof
           -> Bool
constraint (trs,modelValues) (Proof model orders) = 
    case makeLabeledTrs model trs modelValues of
        (labeledTrs, isModel) -> isModel &&
            couldDeleteOneRule ( steps ( tagAll labeledTrs ) orders )

couldDeleteOneRule
  :: TaggedGroupedTrs Symbol Symbol label -> Bool
couldDeleteOneRule trs = case trs of
    TaggedGroupedTrs rss -> exists rss ( \ rs -> 
        forall rs ( \ r -> case r of (tag,rule) -> not tag && isMarkedRule rule ) )

tagAll
  :: GroupedTrs var node label -> TaggedGroupedTrs var node label
tagAll trs = case trs of 
    GroupedTrs rss -> 
        TaggedGroupedTrs (map (map ( \ rule -> (True,rule))) rss)

steps
  :: TaggedGroupedTrs Symbol Symbol Label
     -> [(Map MSL Bool, TerminationOrder MSL)]
     -> TaggedGroupedTrs Symbol Symbol Label
steps trs orders = foldl step trs orders 

-- | check that all usable rules are tagged (if not, raise exception).
-- check that all (marked and unmarked) tagged rules 
-- are weakly compatible with order (if not, raise exception).
-- then untag the marked rules that are strictly compatible.

step
  :: TaggedGroupedTrs Symbol Symbol Label
     -> (Map MSL Bool, TerminationOrder MSL)
     -> TaggedGroupedTrs Symbol Symbol Label
step trs (usable,order) = case usableOK trs usable of
    False -> undefined
    True -> 
        let utrs = tagUsable trs usable 
        in  case weaklyCompatibleOK utrs order of
                False -> undefined
                True  -> untagStrictlyCompatible utrs order

weaklyCompatibleOK
  :: TaggedGroupedTrs Symbol Symbol Label
     -> TerminationOrder MSL -> Bool
weaklyCompatibleOK (TaggedGroupedTrs rss) order = 
    forall rss ( \ rs -> forall rs ( \ r -> case r of 
        ( tag, rule ) -> not tag || isWeaklyCompatible order rule ))
    
untagStrictlyCompatible
  :: TaggedGroupedTrs Symbol Symbol Label
     -> TerminationOrder MSL
     -> TaggedGroupedTrs Symbol Symbol Label
untagStrictlyCompatible ( TaggedGroupedTrs rss ) order = 
    TaggedGroupedTrs 
        ( for rss ( \ rs -> for rs ( \ r -> case r of
             (tag,rule) -> ( tag && not ( isStrictlyCompatible order rule ), rule)  )))

-- * Usable rules

-- | tag all unmarked rules that are usable (according to table)
-- keep tags for marked rules.
tagUsable (TaggedGroupedTrs rss) usable = TaggedGroupedTrs (
    for rss ( \ rs -> for rs ( \ ( tag, rule ) -> 
      case assertKnown ( isMarkedRule rule ) of
        True -> ( tag, rule ) -- keep the previous tag (rule might already be removed)
        False -> case rule of
            Rule _ lhs rhs -> case assertKnown lhs of 
                Var v -> undefined -- cannot happen (at top of lhs)
                Node sym lab ts -> ( lookup eqMSL (sym,lab) usable, rule ) ) ) )


require_all_usable (TaggedGroupedTrs rss) usable = 
    forall usable ( \ (k,v) -> v ) 

-- | check that the usable (unmarked) rules are tagged in the table
usableOK
  :: TaggedGroupedTrs Symbol Symbol Label
     -> Map MSL Bool -> Bool
usableOK (TaggedGroupedTrs rss) usable = forall rss ( \ rs -> forall rs ( \ (tag,rule) -> 
    case rule of 
      Rule isMarked lhs rhs -> 
        let -- for marked rules, left top symbol must be usable 
            left_ok = implies (isMarked && tag) ( case lhs of
                Var v -> undefined -- should not happen (no lhs can be Var)
                Node sym lab ts -> lookup eqMSL (sym,lab) usable  )
            -- if left top symbol is usable, then all syms in rhs must be usable
            right_ok = case lhs of 
                Var v -> undefined
                Node sym lab ts -> 
                    implies (lookup eqMSL (sym,lab) usable)
                        ( forallSubterms rhs ( \ s -> case s of
                             Var v -> True
                             Node sym lab ts -> lookup eqMSL (sym,lab) usable ))
        in  left_ok && right_ok  ) )


-- * make labeled TRS & search model

assignements :: [Symbol] -> [Domain] -> Assignments Symbol
assignements syms values = case syms of
  []   -> [[]]
  s:ss -> concatMap (\as -> concatMap (\v -> [(s,v) : as]) values) 
                    (assignements ss values)

makeLabeledTrs :: Model Symbol -> DPTrs () -> [Domain] -> (GroupedDPTrs Label, Bool)
makeLabeledTrs model (Trs rules) modelValues = 
  case unzip (map (\r -> makeLabeledRule model r modelValues) rules) of
    (rules', equalities) -> (GroupedTrs rules', and equalities)

makeLabeledRule :: Model Symbol -> DPRule () -> [Domain] -> ([DPRule Label], Bool)
makeLabeledRule model (Rule isMarked lhs rhs) modelValues = 
  let sigmas       = assignements (variables lhs) modelValues
      goRule sigma = case makeLabeledTerm model lhs sigma of
        (lhs', lhsValue) -> case makeLabeledTerm model rhs sigma of
          (rhs', rhsValue) -> (Rule isMarked lhs' rhs', eqValue lhsValue rhsValue)
  in
    case unzip (map goRule sigmas) of
      (rules', equalities) -> (rules', and equalities)

makeLabeledTerm :: Model Symbol -> DPTerm () -> Sigma Symbol -> (DPTerm Label, Domain)
makeLabeledTerm model term sigma = case term of
  Var s         -> (Var s, valueOfVar s sigma)
  Node s _ args -> case unzip (map (\a -> makeLabeledTerm model a sigma) args) of
    (args', argsValues) -> (Node s argsValues args', valueOfFun s argsValues model)

valueOfTerm :: Model Symbol -> Sigma Symbol -> DPTerm () -> Domain
valueOfTerm model sigma term = case term of
  Var v           -> valueOfVar v sigma
  Node sym l args -> case l of 
    () -> let values = map (valueOfTerm model sigma) args
          in
            valueOfFun sym values model

valueOfFun :: Symbol -> [Domain] -> Model Symbol -> Domain
valueOfFun s args model = 
  let interp     = interpretation s model
      argPattern = map Exactly args
  in
    lookup (\xs ys -> and (zipWith (eqPattern eqValue) xs ys)) argPattern interp

valueOfVar :: Symbol -> Sigma Symbol -> Domain
valueOfVar = lookup eqSymbol

interpretation :: Symbol -> Model Symbol -> Interpretation
interpretation = lookup eqSymbol

-- * filter arguments

filterArgumentsDPTrs :: ArgFilter MSL -> DPTrs Label -> DPTrs Label
filterArgumentsDPTrs filter (Trs rules) = 
  let goRule (Rule isMarked lhs rhs) = Rule isMarked
                                         (filterArgumentsDPTerm filter lhs) 
                                         (filterArgumentsDPTerm filter rhs)
  in
    Trs (map goRule rules)

filterArgumentsDPTerm :: ArgFilter MSL -> DPTerm Label -> DPTerm Label
filterArgumentsDPTerm filter term = case term of
  Var v         -> Var v
  Node s l args -> 
    let flt = lookup eqLabeledSymbol (s,l) filter
    in  case flt of
     Selection indices -> 
      Node s l (map (\i -> filterArgumentsDPTerm filter (atIndex i args)) indices)
     Projection i -> 
      filterArgumentsDPTerm filter (atIndex i args)

-- * check compatibility with order

isWeaklyCompatible
  :: TerminationOrder MSL -> Rule Symbol Symbol Label -> Bool
isWeaklyCompatible order (Rule isMarked lhs rhs) = 
       let cmp = case order of
             LinearInt int -> 
                 linearRule int (Rule isMarked lhs rhs) 
             FilterAndPrec f p ->
                 lpo p (filterArgumentsDPTerm f lhs) (filterArgumentsDPTerm f rhs) 
       in case cmp of
              Gr  -> True
              Eq  -> True
              NGe -> False

isStrictlyCompatible
  :: TerminationOrder MSL -> Rule Symbol Symbol Label -> Bool
isStrictlyCompatible order (Rule isMarked lhs rhs) = isMarked &&
       let cmp = case order of
             LinearInt int -> linearRule int (Rule isMarked lhs rhs) 
             FilterAndPrec f p ->
                 lpo p (filterArgumentsDPTerm f lhs) (filterArgumentsDPTerm f rhs) 
       in case cmp of
              Gr  -> True
              Eq  -> False
              NGe -> False

isMarkedRule :: Rule Symbol Symbol label -> Bool
isMarkedRule (Rule isMarked lhs rhs) = isMarked

-- * order from linear interpretation
-- FIXME: at the moment, this handles only unary functions (enough for SRS)
-- FIXME: bit width (3) is hardwired (in linearTerm below)

linearRule :: LinearInterpretation MSL -> DPRule Label -> Order
linearRule int (Rule m lhs rhs) = 
    let vars = varRule (Rule m lhs rhs)
        -- the linear functions inside this block
        -- use the ordering of the variables in vars,
        -- e.g., with  vars = [x,y,z] , 
        -- the term  y  is LinearFunction 0 [0,1,0]
    in  case linearTerm int vars lhs of
        LinearFunction labs llins -> 
            case linearTerm int vars rhs of
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


varRule :: DPRule a -> [ Symbol ]
varRule (Rule _ lhs rhs) = varTerm lhs ( varTerm rhs [] )

varTerm :: DPTerm a -> [ Symbol ] -> [ Symbol ]
varTerm t vs = case {- assertKnown -} t of
    Var v -> insert v vs
    Node f lf args -> varTerms args vs

varTerms :: [ DPTerm a ] -> [ Symbol ] -> [ Symbol ]
varTerms ts vs = case {- assertKnown -} ts of
    [] -> vs
    t : ts' -> varTerm t ( varTerms ts' vs )

insert :: Symbol -> [ Symbol ] -> [ Symbol ]
insert v ws = case {- assertKnown -} ws of
    [] -> [v]
    w : ws' -> 
        -- if eqSymbol v w then ws else w : insert v ws'
        case {- assertKnown -} ( eqSymbol v w ) of 
            True -> ws ; False -> w : insert v ws' 
            

linearTerm :: LinearInterpretation MSL -> [ Symbol ] -> DPTerm Label -> LinearFunction
linearTerm int vars t = case t of
    Var x ->  
        LinearFunction (nat 5 0) ( map ( \ v -> eqSymbol v x) vars )
    Node f lf args -> 
        let int_f = lookup eqLabeledSymbol (f, lf) int
            values = map ( linearTerm int vars) args
        in  substitute vars int_f values

absolute (LinearFunction abs lin) = abs
linear (LinearFunction abs lin) = lin

substitute :: [ Symbol ] -> LinearFunction -> [ LinearFunction ] -> LinearFunction
substitute vars f gs = case f of 
    LinearFunction fabs flins -> 
        let l0 = LinearFunction (nat 5 0) (map (\v -> False) vars)
            s = foldr plusL l0 ( zipWith scaleL flins gs)
        in  LinearFunction (plusNat fabs (absolute s)) (linear s)

scaleL f (LinearFunction abs lin) = 
    LinearFunction (timesBoolNat f abs) (map (timesBoolBool f) lin)

plusL (LinearFunction a1 l1) (LinearFunction a2 l2) =
    LinearFunction (plusNat a1 a2) (zipWith plusBoolBool l1 l2)

plusBoolBool a b = case a of
    False -> b
    True -> case b of
         False -> True
         True -> undefined

timesBoolBool a b = a && b

timesBoolNat b n = case b of
    False -> nat 5 0 
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
ord precedence a b = case precedence of
    EmptyPrecedence -> case eqLabeledSymbol a b of
        True -> Eq
        False -> NGe
    Precedence prec -> 
        let pa = lookup eqLabeledSymbol a prec
            pb = lookup eqLabeledSymbol b prec
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

variables :: Term Symbol n l -> [Symbol]
variables = 
  let go vs term = case term of
        Var v -> case isElem eqSymbol v vs of
                  True  -> vs
                  False -> v:vs

        Node _ _ args -> foldl go vs args
  in
    go []

isElem :: (a -> a -> Bool) -> a -> [a] -> Bool
isElem eq x xs = case xs of
  []   -> False
  y:ys -> case eq x y of True  -> True
                         False -> isElem eq x ys

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

eqLabeledSymbol :: MSL -> MSL -> Bool
eqLabeledSymbol (s,l) (s',l') = (eqSymbol s s') && (eqLabel l l')

eqMSL :: MSL -> MSL -> Bool
eqMSL = eqLabeledSymbol 

eqLabeledDPTerm :: DPTerm Label -> DPTerm Label -> Bool
eqLabeledDPTerm = eqTerm eqSymbol eqSymbol eqLabel

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

eqSymbol :: Symbol -> Symbol -> Bool
eqSymbol = eqNat

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

implies p q = not p || q

eqPattern :: (k -> k -> Bool) -> Pattern k -> Pattern k -> Bool
eqPattern f x y = case x of
  Any        -> True
  Exactly x' -> case y of
    Any        -> True
    Exactly y' -> f x' y'

forallSubterms t p = p t && case {- assertKnown -} t of
    Var v -> True
    Node sym lab ts -> forall ts ( \ t -> forallSubterms t p )

exists :: [a] -> (a -> Bool) -> Bool
exists xs f = any f xs

forall :: [a] -> (a -> Bool) -> Bool
forall xs f = all f xs

for :: [a] -> (a -> b) -> [b]
for xs f = map f xs

