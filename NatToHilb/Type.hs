module NatToHilb.Type where
import Data.List
import Data.Maybe

-- simples types with sum, product and bottom type
data Type = Base Int
          | Arrow Type Type
          | Product Type Type
          | Sum Type Type
          | Bot deriving (Eq, Read, Show)

-- (appearsin x n) if (Base n) appears in x
appearsin :: Type -> Int -> Bool
appearsin (Base n) m = (n == m)
appearsin (Arrow x y) m = or [appearsin x m, appearsin y m]
appearsin (Product x y) m = or [appearsin x m, appearsin y m]
appearsin (Sum x y) m = or [appearsin x m, appearsin y m]
appearsin Bot m = False

-- (subs x n y) substitutes occurences of (Base n) with y
subs :: Type -> Int -> Type -> Type
subs (Base n) m y = if (n == m) then y else (Base n)
subs (Arrow x1 x2) m y = Arrow (subs x1 m y) (subs x2 m y)
subs (Product x1 x2) m y = Product (subs x1 m y) (subs x2 m y)
subs (Sum x1 x2) m y = Sum (subs x1 m y) (subs x2 m y)
subs Bot m y = Bot

-- (unify [] l1) applies the Martelli/Montanari unification algorithm
-- to the set of equations l1
unify :: [(Type, Type)] -> [(Type, Type)] -> Maybe [(Type, Type)]
unify l1 ((Base n, x) : l2) = if (appearsin x n) then
                                Nothing
                              else
                                let mapsubs = (map (\w -> let (w1, w2) = w in (subs w1 n x, subs w2 n x))) in
                                  let appearsinlist = (\lx -> or $ map (\w -> let (w1, w2) = w in or [appearsin w1 n, appearsin w2 n]) lx) in
                                    if (not $ appearsinlist l1) then
                                      unify ((Base n, x) : l1) (mapsubs l2)
                                    else
                                      unify [] ((mapsubs l1) ++ [(Base n, x)] ++ (mapsubs l2))
unify l1 ((x, Base n) : l2) = unify l1 ((Base n, x) : l2)
unify l1 (((Arrow x1 x2), y) : l2) = case y of
                                       Arrow y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                       _ -> Nothing
unify l1 (((Product x1 x2), y) : l2) = case y of
                                         Product y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                         _ -> Nothing
unify l1 (((Sum x1 x2), y) : l2) = case y of
                                     Sum y1 y2 -> unify l1 ((x1, y1) : (x2, y2) : l2)
                                     _ -> Nothing
unify l1 ((Bot, y) : l2) = case y of
                             Bot -> unify l1 l2
                             _ -> Nothing
unify l1 [] = Just l1 -- end condition

-- returns list of base types inside a type
basetypes :: Type -> [Int]
basetypes (Base n) = [n]
basetypes (Arrow x y) = (basetypes x) ++ (basetypes y)
basetypes (Product x y) = (basetypes x) ++ (basetypes y)
basetypes (Sum x y) = (basetypes x) ++ (basetypes y)
basetypes Bot = []

