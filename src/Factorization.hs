


module Factorization where
    

import           Data.List              (group,transpose,sort)

import           Data.Map               ( adjust
                                        , assocs
                                        , delete
                                        , filter
                                        , fromListWith
                                        , insert
                                        , intersectionWith
                                        , lookup
                                        , Map
                                        , member
                                        )

import qualified Data.Set            as S
import           Protolude       hiding (filter)


newtype Factorized a = Factorized [Polinomy a] deriving(Show,Eq,Ord,Read,Monoid)
newtype Polinomy   a = Polinomy   [Monomy   a] deriving(Show,Eq,Ord,Read,Monoid)
newtype Monomy     a = Monomy     [a]          deriving(Show,Eq,Ord,Read,Monoid)

data ProblemState a = ProblemState
        { suitableMonomy   :: [Monomy a]                
                                                        

        , requiredMonomy   :: Map (Monomy a             
                                  )                     
                                  
                                  ( Sum Int 
                                  , Set ( Monomy a       
                                        , Monomy a       
                                        )
                                  )      
                                                        
        
        , dependency       :: Map ( Monomy a            
                                  )                           
                                  ( Set                 
                                        ( Monomy a          
                                        , Monomy a
                                        )               

                                  )
        
        , polynomy_a       :: [Monomy a]

        , polynomy_b       :: [Monomy a]
        
        } deriving(Show,Eq,Ord,Read)

factorize::(Ord a,Show a) => Polinomy   a -> Factorized a
factorize (Polinomy [a]) = Factorized [Polinomy [a]]
factorize pol            = case factor_step =<< initialize_problem pol of
                            
                            (a,b) : _ -> factorize a <> factorize b 

                            []        -> Factorized [pol]




initialize_problem :: (Ord a) => Polinomy   a -> [(ProblemState a)]
initialize_problem poly = [ ProblemState
                               { suitableMonomy  = all_possible
                               , requiredMonomy  = required
                               , dependency      = depends'
                               , polynomy_a      = [a]
                               , polynomy_b      = [b] 
                               }

                          | (a,b,Polinomy poly') <- choose_headers poly
                                                -- TODO: reverse?
                          , let all_possible  = sort$ordNub $ poly' >>= expand_factors

                                required_b    = let Polinomy xs = poly
                                                 in filter (>0)
                                                  . fromListWith (<>) 
                                                  $ (multiply a b, Sum (-1)) : [ (x, Sum 1)|x<-xs]


                                required_a    = fromListWith (<>)
                                                [ ( multiply a b
                                                  , ( S.singleton (min a b, max a b)
                                                    ) 
                                                  )

                                                | a <- all_possible
                                                , b <- all_possible
                                                ]

                                required      = intersectionWith (,) required_b required_a
                                 
                                depends       = compose_map 
                                                [ (a',(p,b'))
                                                
                                                | (p,  (_, val) ) <- assocs required
                                                , (a, b)          <- toList val
                                                , (a', b')        <- [(a, b),(b, a)]
                                                ]

                                depends'      = insert a S.empty $ insert b S.empty depends  
                          ]


compose_map :: (Ord a) => [(Monomy a, (Monomy a, Monomy a))] 
                       -> Map (Monomy a) (Set (Monomy a, Monomy a))
compose_map xs = fromListWith S.union [ (key,S.singleton val) | (key,val)<- xs]


multiply :: (Ord a) => Monomy a -> Monomy a -> Monomy a
multiply  (Monomy a) (Monomy b)    = Monomy . sort $ a ++ b 


expand_factors :: (Ord a) => Monomy a -> [Monomy a]
expand_factors x = sort$ordNub [ x | (a,b) <- feasible_products x, x <- [a,b]]


feasible_products :: (Ord a) =>Monomy a -> [(Monomy a,Monomy a)]  
feasible_products (Monomy xs) = [ (Monomy a,Monomy b) 
                                | (a,b) <- feasible_products' (group $ sort xs)
                                , a >= b
                                ]
  where
    feasible_products' xs = case xs of
                                   
                               e : es -> [ (a++as,b++bs)
                                         | n          <- [0..length e]
                                         , let (a,b)   = splitAt n e
                                         , (as,bs)    <- feasible_products' es
                                         ]

                               []     -> [([],[])]                              


factor_step :: (Ord a) => ProblemState a -> [(Polinomy a,Polinomy a)]
factor_step st    = if null (requiredMonomy st) 

                       then if elem [Monomy []] [polynomy_a st,polynomy_b st]
                             
                             then [] -- we hace no factorized shit!!

                             else [ ( Polinomy (polynomy_a st)
                                    , Polinomy (polynomy_b st)
                                    )
                                  ]
                       
                       else [ sol
                            | Just st' <- [ monomy_to_a st
                                          , monomy_to_b st
                                          , drop_monomy st
                                          ]
                            , sol      <- factor_step st'
                            ]

monomy_to_a :: (Ord a) => ProblemState a -> Maybe (ProblemState a)
monomy_to_a st = case suitableMonomy st of
                   
                   x : xs -> do let new_products  =  [multiply x b | b <- polynomy_b st]

                                requiredMonomy'  <- foldrM dropRequired (requiredMonomy st) new_products 
                                 
                                return $ st{ suitableMonomy = xs
                                           , requiredMonomy = requiredMonomy' 
                                           , polynomy_a     = x : polynomy_a st 
                                           }
                   
                   []     -> Nothing


monomy_to_b :: (Ord a) => ProblemState a -> Maybe (ProblemState a)
monomy_to_b = fmap switch . monomy_to_a . switch
  where
    switch st = st{ polynomy_a = polynomy_b st
                  , polynomy_b = polynomy_a st
                  }



drop_monomy :: (Ord a) => ProblemState a -> Maybe (ProblemState a)
drop_monomy st = case suitableMonomy st of

                   x : xs 
                       | Just depends <- lookup x (dependency st)
                       , Just st'     <- foldrM (dropDepend x) st depends -> Just st'{suitableMonomy = xs}  
                       
                       | Nothing      <- lookup x (dependency st)         -> error "This was not supposed to be possible!"

                   _                                                      -> Nothing


dropDepend     :: (Ord a) => Monomy a -> (Monomy a, Monomy a ) -> ProblemState a -> Maybe (ProblemState a)
dropDepend   a (p,b)  st = case lookup p (requiredMonomy st) of 

                            Just (n,set) -> let set'    = S.delete (a',b') set 
                                                (a',b') = (min a b, max a b)

                                             in if | S.null set'             -> Nothing
                                                   | S.notMember (a',b') set -> error "imposible branch!! "
                                                   | otherwise               -> Just st
                                                                                  { requiredMonomy = insert p (n,set') (requiredMonomy st)
                                                                                  
                                                                                  , dependency     = adjust (S.delete (p,a)) b (dependency st) 
                                                                                  
                                                                                  }
                            Nothing                                      -> Just st



choose_headers :: (Ord a) =>  Polinomy a -> [(Monomy a, Monomy a, Polinomy a)]
choose_headers (Polinomy xs )= case snd <$> sort [ (size x,x)|x <- xs] of 
                                 
                                 y : ys -> [ (a,b,Polinomy ys) | (a,b) <- feasible_products y]

                                 []     -> []
  where
    size (Monomy xs) = product [ length x + 1 | x <- group (sort xs)]


dropRequired :: ( Ord a
              
                ) => Monomy a
                  -> Map (Monomy a) (Sum Int,Set (Monomy a, Monomy a)) 
                  -> Maybe (Map (Monomy a) (Sum Int,Set (Monomy a, Monomy a)))

dropRequired x m = case lookup x m of
                     
                     Just (n,set) 
                       | n > 1     -> Just $ insert x (n-1,set) m
                       | otherwise -> Just $ delete x           m

                     Nothing       -> Nothing


















