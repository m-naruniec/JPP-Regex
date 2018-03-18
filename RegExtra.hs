module RegExtra where
import Mon
import Reg
import Data.List

data AB = A | B deriving (Eq, Ord, Show)

infix 4 ===
class Equiv a where
  (===) :: a -> a -> Bool

instance (Eq c) => Equiv (Reg c) where
  r1 === r2 = (simpl r1) == (simpl r2)

instance Mon (Reg c) where
  m1 = Eps
  (<>) = (:>)

simpl :: Eq c => Reg c -> Reg c
simpl = altsReg . simpl'
    where
        altsReg :: [Reg c] -> Reg c
        altsReg = foldr1 (:|)

        simpl' :: Eq c => Reg c -> [Reg c]
        simpl' (Many r) =
            case rList of
                [] -> [Eps]
                [Empty] -> [Eps]
                l@[Many _] -> l
                l -> [Many $ altsReg l]
            where
                rList = filter (/= Eps) $ simpl' r
        simpl' ((r1 :> r2) :> r3) = simpl' (r1 :> (r2 :> r3))
        simpl' (r1 :> r2) =
            case (r1List, r2List) of
                ([Empty], _) -> [Empty]
                (_, [Empty]) -> [Empty]
                ([Eps], l) -> l
                (l, [Eps]) -> l
                (l1, l2) -> [(altsReg l1) :> (altsReg l2)]
            where
                r1List = simpl' r1
                r2List = simpl' r2
        simpl' (r1 :| r2) =
            case (r1List, r2List) of
                ([Empty], l) -> l
                (l, [Empty]) -> l
                (l1, l2) -> union l1 l2
            where
                r1List = simpl' r1
                r2List = simpl' r2
        simpl' r = [r]


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


der :: Eq c => c -> Reg c -> Reg c
der _ Empty = Empty
der _ Eps = Empty
der c (Lit l)
    | c == l = Eps
    | otherwise = Empty
der c (Many r) = (der c r) :> (Many r)
der c (r1 :> r2) =
    if nullable r1
        then notNull :| r2'
        else notNull
    where
        r1' = der c r1
        r2' = der c r2
        notNull = r1' :> r2
der c (r1 :| r2) = (der c r1) :| (der c r2)

ders :: Eq c => [c] -> Reg c -> Reg c
ders w r = foldl f r' w
    where
        r' = simpl r
        f rf c = simpl $ der c rf


accepts :: Eq c => Reg c -> [c] -> Bool
accepts r w = nullable $ ders w r

mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = not $ empty $ der c r

match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w =
    reverse <$> (third $ foldl f (r', [], startBest) w)
    where
        r' = simpl r
        third (_, _, z) = z
        startBest = if nullable r' then Just [] else Nothing
        f (rf, pref, best) c = (rf', pref', best')
            where
                rf' = simpl $ der c rf
                pref' = c:pref
                best' = if nullable rf' then Just pref' else best

-- works as search but also returns number of chars before match
indexedSearch :: Eq c => Reg c -> [c] -> (Maybe [c], Int)
indexedSearch r = foldl f (Nothing, -1) . tails
    where
        f (Nothing, i) t = (match r t, i + 1)
        f acc _ = acc

search :: Eq c => Reg c -> [c] -> Maybe [c]
search r = fst . indexedSearch r

findall :: Eq c => Reg c -> [c] -> [[c]]
findall r = reverse . fst . foldl f ([], 0) . delete [] . tails
    where
        f (l, 0) t =
            if matched == Nothing
                then (l, trash)
                else (matched':l, trash)
            where
                (matched, i) = indexedSearch r t
                (Just matched') = if matched == Nothing
                                     then Just []
                                     else matched
                trash = max (i + (length matched') - 1) 0
        f (l, trash) _ = (l, trash - 1)


char :: Char -> Reg Char
char = Lit

string :: [Char] -> Reg Char
string = foldr1 (:>) . map Lit

alts :: [Char] -> Reg Char
alts = foldr1 (:|) . map Lit

letter :: Reg Char
letter = alts ['a'..'z'] :| alts ['A'..'Z']

digit :: Reg Char
digit = alts ['0'..'9']

number :: Reg Char
number = digit :> Many digit

ident :: Reg Char
ident = letter :> Many (letter :| digit)

many1 :: Reg c -> Reg c
many1 r = r :> Many r

