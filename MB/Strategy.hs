module MB.Strategy where

import TPDB.Data

import Text.PrettyPrint.HughesPJ

type Remover v s t = TRS v s 
                 -> IO ( Maybe ( Doc, Maybe (TRS v t) ) )




andthen f g sys0 = do
    x <- f sys0
    case x of
        Nothing -> return Nothing
        Just (p, m) -> case m of
            Nothing -> return $ Just ( p, m )
            Just sys1 -> do
                y <- g sys1
                case y of
                    Nothing -> return Nothing
                    Just (q, m) -> return $ Just ( p $$ q, m )

orelse f g sys0 = do
    x <- f sys0
    case x of
        Nothing -> g sys0
        Just (p,m) -> return $ Just (p,m)
