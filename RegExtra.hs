module RegExtra where
import Mon
import Reg
import Data.List
import Data.Functor -- TODO remove

data AB = A | B deriving(Eq,Ord,Show)

infix 4 ===
class Equiv a where
  (===) :: a -> a -> Bool

instance (Eq c) => Equiv (Reg c) where
  r1 === r2 = (simpl r1) == (simpl r2)

instance Mon (Reg c) where
  m1 = Eps
  (<>) = (:>)

listToReg :: [Reg c] -> Reg c
listToReg = foldr1 (:|)

simpl :: Eq c => Reg c -> Reg c
simpl = listToReg . simpl'

--simplConcats :: Reg c -> Reg c
--simplConcats ((r1 :> r2) :> r3) = (r1 :> (r2 :> r3))
--simplConcats (r1 :> r2) = (simplConcats r1) :> (simplConcats r2)
--simplConcats r = r

simpl' :: Eq c => Reg c -> [Reg c]
simpl' (Many r) =
    case rList of
        [Eps] -> [Eps]
        [Empty] -> [Eps]
        -- ...TODO
        r'@[Many _] -> r'
        r' -> [Many $ listToReg r']
    where
        rList = nub $ map (\x -> case x of {(Many y) -> y; y -> y}) $ simpl' r--filter (/= Eps) $ simpl' r
simpl' ((r1 :> r2) :> r3) = simpl' (r1 :> (r2 :> r3))
simpl' (r1 :> r2) =
    case (r1List, r2List) of
        ([Empty], _) -> [Empty]
        (_, [Empty]) -> [Empty]
        ([Eps], r) -> r
        (r, [Eps]) -> r
        -- Many Many ? chyba nie zadziala dla ponizszego
--        ([r1' :> r2'], r3') -> [r1' :> r2'']
--            where r2'' = (head(simpl' (r2' :> (listToReg r3'))))
        (r1', r2') -> [((listToReg r1') :> (listToReg r2'))]
    where
        r1List = simpl' r1
        r2List = simpl' r2

simpl' (r1 :| r2) =
    case (r1List, r2List) of
        ([Empty], r2') -> r2'
        (r1', [Empty]) -> r1'
        (r1', r2') -> union r1' r2'
    where
        r1List = simpl' r1
        r2List = simpl' r2

simpl' r = [r]


--simpl (Many r) = simpl' (Many (simpl r))
--simpl (r1 :> r2) = simpl' ((simpl r1) :> (simpl r2))
--simpl (r1 :| r2) = simpl' ((simpl r1) :| (simpl r2))
--simpl r = r
--
--simpl' :: Eq c => Reg c -> Reg c
--simpl' (Eps :> r) = r
--simpl' (r :> Eps) = r
--simpl' (Empty :> r) = Empty
--simpl' (r :> Empty) = Empty
--simpl' (Empty :| r) = r
--simpl' (r :| Empty) = r
--simpl' (Many (Eps)) = Eps
--simpl' (Many (Empty)) = Eps
--simpl' (Many (Many r)) = Many r
--simpl' (Eps :| (Many r)) = Many r
--simpl' ((Many r) :| Eps) = Many r
--simpl' r@(Many (Lit c1) :> Many (Lit c2))
--    | c1 == c2 = Many (Lit c1)
--    | otherwise = r
--simpl' r@((Many r1) :> (Many r2))
--   | r1 == r2 = (Many r1)
--   | otherwise = r
--simpl' ((r1 :> r2) :> r3) = simpl' (r1 :> (simpl' (r2 :> r3)))
--simpl' ((r1 :| r2) :| r3) = simpl' (r1 :| (simpl' (r2 :| r3)))
--simpl' (r1 :> (r2 :> r3)) = simpl' ((simpl' (r1 :> r2)) :> r3)
--simpl' (r1 :| (r2 :| r3)) = simpl' ((simpl' (r1 :| r2)) :| r3)
--simpl' r@(r1 :| r2)
--   | r1 == r2 = r1
--   | otherwise = r
--simpl' r = r


nullable :: Reg c -> Bool
nullable Empty = False
nullable Eps = True
nullable (Lit _) = False
nullable (Many _) = True
nullable (r1 :> r2) = (nullable r1) && (nullable r2)
nullable (r1 :| r2) = (nullable r1) || (nullable r2)

empty :: Reg c -> Bool
empty Empty = True
empty Eps = False
empty (Lit _) = False
empty (Many _) = False
empty (r1 :> r2) = (empty r1) || (empty r2)
empty (r1 :| r2) = (empty r1) && (empty r2)


--der :: Eq c => c -> Reg c -> Reg c
--der c r = fst $ der' c r
--
--der' :: Eq c => c -> Reg c -> (Reg c, Bool)
--der' _ Empty = (Empty, False)
--der' _ Eps = (Empty, True)
--der' c (Lit l)
--    | c == l = (Eps, False)
--    | otherwise = (Empty, False)
--
--der' c (Many r) = ((simpl' $ (der c r) :> (Many r)), True)
--der' c (r1 :> r2) =
--    if r1Nullable
--        then ((simpl' $ notNulled :| r2'), r2Nullable)
--        else (notNulled, False)
--    where
--        (r1', r1Nullable) = der' c r1
--        (r2', r2Nullable) = der' c r2
--        notNulled = simpl' $ r1' :> r2
--der' c (r1 :| r2) = ((simpl' $ r1' :| r2'), (r1Nullable || r2Nullable))
--    where
--        (r1', r1Nullable) = der' c r1
--        (r2', r2Nullable) = der' c r2


der :: Eq c => c -> Reg c -> Reg c
der _ Empty = Empty
der _ Eps = Empty
der c (Lit l)
    | c == l = Eps
    | otherwise = Empty
der c (Many r) = (der c r) :> (Many r)
der c (r1 :> r2) =
    if nullable r1
        then notNulled :| r2'
        else notNulled
    where
        r1' = der c r1
        r2' = der c r2
        notNulled = r1' :> r2
der c (r1 :| r2) = (der c r1) :| (der c r2)

ders :: Eq c => [c] -> Reg c -> Reg c
ders c r = foldl f r' c
    where
        r' = simpl r
        f rf c = simpl $ der c rf


accepts :: Eq c => Reg c -> [c] -> Bool
accepts r w = nullable $ ders w r

mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = not $ empty $ der c r

match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w = Nothing
--    if empty r'
--        then Nothing
--        else Just $ reverse $ snd $ foldl f (r', []) w
--    where
--        r' = simpl r
--        f (rf, pref) c = (rf', pref')
--            where
--                rf' = simpl $ der c rf
--                pref' = if empty rf' then pref else c:pref

search :: Eq c => Reg c -> [c] -> Maybe [c]
search r w = Nothing
--    if matches == []
--        then Nothing
--        else Just $ fst $ foldl f ([], 0) matches
--    where
--        matches = findall r w
--        f old@(_, maxLen) l = if len > maxLen then (l, len) else old
--            where len = length l

findall :: Eq c => Reg c -> [c] -> [[c]]
findall r w = [[]]
--    fromJust <$> (filter (/= Nothing) $ match r' <$> tails w)
--    where
--        r' = simpl r
--        fromJust (Just l) = l
--        fromJust _ = []


char :: Char -> Reg Char
char = Lit

string :: [Char] -> Reg Char
string = foldr1 (:>) . map Lit

alts :: [Char] -> Reg Char
alts = foldr1 (:|) . map Lit

letter = alts ['a'..'z'] :| alts ['A'..'Z']
digit = alts ['0'..'9']
number = digit :> Many digit
ident = letter :> Many (letter :| digit)

many1 r = r :> Many r

