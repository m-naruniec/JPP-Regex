module RegExtra where
import Mon
import Reg
import Data.List

data AB = A | B deriving(Eq,Ord,Show)

infix 4 ===
class Equiv a where
  (===) :: a -> a -> Bool

instance (Eq c) => Equiv (Reg c) where
  r1 === r2 = (simpl r1) == (simpl r2)

instance Mon (Reg c) where
  m1 = Eps
  (<>) = (:>)

simpl :: Reg c -> Reg c
simpl x = x

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

-- continue
der :: Eq c => c -> Reg c -> Reg c
der _ Empty = Empty
der _ Eps = Empty
der c (Lit l)
    | c == l = Eps
    | otherwise = Empty
der c r = r

-- may need simpl
ders :: Eq c => [c] -> Reg c -> Reg c
ders = flip $ foldl $ flip der

accepts :: Eq c => Reg c -> [c] -> Bool
accepts r w = nullable $ ders w r

mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = not $ empty $ der c r

match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w = Nothing

search :: Eq c => Reg c -> [c] -> Maybe [c]
search r w = Nothing

findall :: Eq c => Reg c -> [c] -> [[c]]
findall r w = []

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

