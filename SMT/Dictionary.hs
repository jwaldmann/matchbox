module SMT.Dictionary where

data Domain = Int | Arctic | Tropical | Fuzzy  
    deriving ( Show, Eq )

data Dictionary m num val bool = Dictionary
    { info :: String
    , domain :: Domain
      -- | build a non-negative number
    , number   :: m num
      -- | zero or one
    , small_nn_number :: m num
      -- | -1, 0, 1
    , small_number :: m num
      -- | build any number (possibly negative)
    , any_number :: m num
    , nbits :: Int
    , nconstant :: val -> m num
    , decode :: num -> m val
    , add :: num -> num -> m num
    , times :: num -> num -> m num
    , dot_product :: [num] -> [num] -> m num  
    , positive :: num -> m bool
    , nonnegative :: num -> m bool
    , gt :: num -> num -> m bool
    , ge :: num -> num -> m bool
    -- | numeric equal (not: not equal)
    , neq :: num -> num -> m bool 
    , boolean :: m bool
    , bconstant :: Bool -> m bool
    , and :: [ bool ] -> m bool
    , or :: [ bool ] -> m bool
    , not :: bool -> m bool
    , beq :: bool -> bool -> m bool
    , assert :: [ bool ] -> m ()
    , atmost :: Int -> [bool] -> m bool  
    }
