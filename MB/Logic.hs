{-# language NoMonomorphismRestriction #-}

module MB.Logic where 

import Control.Monad.Logic
import Control.Applicative 
import System.IO

run r = do
    out <- observeManyT 1 r
    return $ case out of
        [] ->  Nothing
        x : _ -> Just x

work w x = do
    out <- observeManyT 1 $ w x
    return $ case out of
        [] ->  Nothing
        (x,f) : _ -> Just $ f x

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

mkWork :: (a -> IO (Maybe b)) -> (a -> LogicT IO b)
mkWork f = \ x -> LogicT $ \ succ fail -> do
    out <- f x
    case out of
        Nothing -> fail
        Just y -> succ y fail

success = \ x -> return (x, id)

andthen0 p q x = p x >>= q

andthen p q = \ x -> do 
    (y,f) <- p x ; (z, g) <- q y ; return (z, f . g)

orelse p q = \ x -> do mplus (p x) (q x)

capture p =  \ x -> once ( p x)

orelse_andthen p q r = \ x -> ifte (p x) q (r x)

reject = mzero

multi p = \ xs -> do
    yfs <- forM xs p
    return ( map fst yfs
           , \ ps -> zipWith ($) (map snd yfs) ps
           )

transformer fore back = mkWork $ \ sys -> return $
     case fore sys of
         Nothing   -> Nothing
         Just sys' -> Just ( sys' , back sys )
