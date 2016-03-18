{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module CFGrammar
  ( term
  , nonterm
  , Term(..)
  , NonTerm(..)
  , Grammar(..)
  , Rule
  , prepare
  , strip
  , generate
  , generateMany
  , emptyTables
  , parse
  , evalParse
  , fromRules
  ) where -- todo

import qualified Data.Map.Strict as M
import Data.Char
import Data.Either
import Data.Maybe
import Data.List (intercalate, nub)
import qualified Data.Set as S

import Control.Monad
import Control.Monad.State
import System.Random

import GHC.Generics (Generic)
import Control.DeepSeq -- for benchmarking



---------------- Types ----------------


data Term = Term Char deriving (Ord, Show, Eq, Generic, NFData)
data NonTerm = NonTerm String deriving (Ord, Show, Eq, Generic, NFData)
type Sym = Either Term NonTerm
type Rule = (NonTerm, [Sym])
type Rules = M.Map NonTerm [[Sym]]
data Grammar = Grammar (NonTerm, Rules) deriving (Show) -- NonTerm is the start symbol

term :: Char -> Sym
term c = Left (Term c)

nonterm :: String -> Sym
nonterm s = Right (NonTerm s)

-- poor man's multimap. todo something better than this.
m_lookup :: Ord k => k -> M.Map k [v] -> [v]
m_lookup k m = case (M.lookup k m) of
  Just vs -> vs
  Nothing -> []

m_insert :: Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
m_insert k v m = M.insert k (v:(m_lookup k m)) m

m_nodup_insert :: Eq v => Ord k => k -> v -> M.Map k [v] -> M.Map k [v] -- not ideal. should have MapToList and MapToSet or something, although we actually are using ordered non-duplicate lists.
m_nodup_insert k v m = M.insert k (nub (v:(m_lookup k m))) m

m_nodup_append :: Eq v => Ord k => k -> v -> M.Map k [v] -> M.Map k [v]
m_nodup_append k v m = M.insert k (nub ((m_lookup k m)++[v])) m

m_assocs :: Ord k => (M.Map k [v]) -> [(k, v)]
m_assocs m = concat $ fmap (\p -> fmap (\v -> (fst p, v)) (snd p)) (M.assocs m)

m_fromList :: Ord k => [(k, v)] -> M.Map k [v]
m_fromList kvs = foldl (\acc (k,v) -> m_insert k v acc) M.empty kvs






---------------- Analysis & Manipulation ----------------


nonterminals :: [Sym] -> [NonTerm]
nonterminals = rights

 -- returns a map from nonterminals to the rules in which they appear. if a nonterminal appears more than once in a rule, the rule will appear more than once in the map
rmap :: Rules -> M.Map NonTerm [Rule]
rmap rs = foldl f M.empty (m_assocs rs)
  where f acc r = foldl (\a x -> m_insert x r a) acc (nonterminals (snd r))



type Nullables = S.Set NonTerm

nullables :: Rules -> Nullables
nullables rs = go cs q (S.fromList q)
  where 
    go :: M.Map Rule Int -> [NonTerm] -> Nullables -> Nullables -- current counts, queue, current known nullables
    go cs [] ns    = ns
    go cs (v:q) ns = case (foldl f (cs, q, ns) (m_lookup v rm)) of (cs', q', ns') -> (go cs' q' ns')

    f :: (M.Map Rule Int, [NonTerm], Nullables) -> Rule -> (M.Map Rule Int, [NonTerm], Nullables)
    f (cs, q, ns) r = case (M.lookup r cs) of
      Nothing -> (cs, q, ns)
      Just 0  -> (cs, q, ns)
      Just 1  -> case r of {(nt, _)
        | S.member nt ns -> (M.insert r 0 cs, q, ns)
        | otherwise      -> (M.insert r 0 cs, nt:q, S.insert nt ns)}
      Just n  -> (M.insert r (n-1) cs, q, ns)

    rm = rmap rs
    cs = counts rs
    q = fmap fst $ M.keys $ M.filter (== 0) cs

    counts :: Rules -> M.Map Rule Int -- map from rules to number of not-known-to-be-nullable symbols in the RHS of that rule (or 0 if the RHS contains terminals)
    counts g = M.fromList $ catMaybes $ fmap counts0 (m_assocs g)
    counts0 (nt, r) 
      | any isLeft r = Nothing
      | otherwise    = Just ((nt, r), length (filter (isRight) r))



-- Find all symbols capable of deriving themselves. If any are present (and reachable), the grammar may have infinitely many parses for a single string. TODO have parse actually check this.
selfDeriving :: Rules -> Nullables -> S.Set NonTerm
selfDeriving rs ns = M.keysSet $ M.filterWithKey (\k vs -> elem k vs) (closure (init rs))
  where 
    m = init rs  -- m[A] contains B iff A *=> B, i.e. it is possible to derive B from A with no extraneous symbols
    init :: Rules -> M.Map NonTerm [NonTerm]
    init rs = foldl f M.empty (m_assocs rs) -- todo maybe replace the multimap with a map-to-set or somesuch
      where
        f acc (nt, prod) = case prod of
          [] -> acc
          (Right nt'):[] -> m_nodup_insert nt nt' acc
          _ | any isLeft prod -> acc
          _ | otherwise -> let nts = (nonterminals prod) in
              case (filter (\x -> not $ S.member x ns) nts) of
                [] -> foldl (\a x -> m_nodup_insert nt x a) acc nts -- everything nullable: everything derivable
                (x:[]) -> m_nodup_insert nt x acc -- exactly one nonnullable: only that is derivable
                _ -> acc -- at least two nonnullables: nothing derivable

    closure :: M.Map NonTerm [NonTerm] -> M.Map NonTerm [NonTerm]
    closure m = m_fromList $ go (M.keys m) (m_assocs m) -- treating m as a collection of reachability information, take its closure (via floyd-warshall)
      where
        go [] es     = es
        go (v:vs) es = go vs (nub (es ++ [(x, y) | (x, a) <- es, (b, y) <- es, a == y]))



data StrippedGrammar = Stripped Grammar deriving (Show) -- should only be constructed by strip

strip :: Grammar -> StrippedGrammar -- todo split this out into `shrink . stripUnit`. Only stripUnit actually nontrivally modifies the grammar (i.e. introduces new rules); shrink is safe to use by the parser.
strip = Stripped . stripDuplicates . stripUnit  -- stripDuplicates . stripUnreachable . stripUseless . stripUnit
  where
    stripUnit (Grammar (s, rs0)) = let rs = m_assocs rs0 in
      case (partitionEithers (fmap unitify rs)) of (n, q) -> Grammar (s, m_fromList $ go n [] q)
        where          
          go :: [Rule] -> [(NonTerm, NonTerm)] -> [(NonTerm, NonTerm)] -> [Rule] -- new rules, seen units, queue units
          go rs _ []        = rs
          go rs s ((a,b):q)
            | a == b    = go rs ((a,b):s) q
            | otherwise = let bprods = m_lookup b rs0 in -- we are eliminating a production of the form A -> B
                case (partitionEithers (fmap (\prod -> unitify (a, prod)) bprods)) of
                  (nrs, nq) -> go (rs ++ nrs) (nub $ (a,b):s) (nub $ (filter (\x -> notElem x s) nq) ++ q)

          unitify (a, ((Right b):[])) = Right (a, b)
          unitify r                   = Left r

    stripUseless = undefined -- todo
    stripUnreachable = undefined
    stripDuplicates (Grammar (s, rs)) = Grammar (s, M.map nub rs)



data DenulledGrammar = Denulled (Bool, StrippedGrammar) -- again, only to be used by denull. bool indicates if the grammar can produce the empty string.

-- Ensure that no symbol can derive the empty string. Potentially exponential blowup, although not common.
-- The combination of denulling and stripping unit productions ensures that no symbol can derive itself, which is also necessary for sampling.
denull :: StrippedGrammar -> Nullables -> DenulledGrammar
denull (Stripped (Grammar (s, rm))) ns =
  let g = (Grammar (s, M.fromList $ fmap (\(k, v) -> (k, v >>= denullprod)) (M.assocs rm))) in
    Denulled ((elem s ns), strip g) -- yes, this time we actually do want M.assocs, god help us. can be done with the multimap versions, but it's more expensive.
  where
    denullprod :: [Sym] -> [[Sym]]
    denullprod ss = filter (/= []) $ filterM (\s -> case s of { (Right nt) | elem nt ns -> [True, False] ; _ -> [True] }) ss -- this is some dark magic. it may help to contemplate `powerset = filterM (const [True, False])`. We want a new rule for every subset of nullable rules on the RHS.



-- Some utility functions
prepare :: Grammar -> DenulledGrammar
prepare g@(Grammar (_, rs)) = denull (strip g) (nullables rs)

fromRules :: [Rule] -> Grammar -- Treats the LHS of the first rule in the list as the start symbol 
fromRules rs@((s, _):_) = Grammar (s, m_fromList rs)

-- Print grammars. todo this, better
pr (Grammar (NonTerm s, rs)) = s ++ "\n" ++ intercalate "\n" (fmap printrules (M.assocs rs))
  where
    printrules (s, rs) = (show s) ++ " \n  -> " ++ intercalate "\n  -> " (fmap (\x -> intercalate ", " (fmap printsym x)) rs)
    printsym (Right (NonTerm s)) = "NT '" ++ s ++ "'"
    printsym (Left (Term c)) = "T '" ++ [c] ++ "'"
prs (Stripped g) = pr g
prn (Denulled (b, s)) = (show b) ++ "\n" ++ prs s





---------------- Sampling ----------------

-- see http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.32.8707
type FTable = M.Map (NonTerm, Int) (M.Map [Sym] Integer) -- NT + length -> number of strings of that length generated by each of its productions
type FPrimeTable = M.Map (Rule, Int, Int) [Integer]
data Tables = Tables { ft :: FTable, fpt :: FPrimeTable } deriving (Generic, NFData) -- the derivings are just to make it benchable, really.

-- Using the provided RNG, generate a string of a given length from the given grammar, potentially augmenting the side tables if necessary.
-- Fails (returns Nothing) the grammar contains no strings of that length, though even in this case the tables may have been augmented.
generateDet :: RandomGen r => DenulledGrammar -> Tables -> Int -> State r (Tables, Maybe String)
generateDet (Denulled (makesEpsilon, Stripped (Grammar (s, rs)))) ts n = case n of
  n | n < 0 -> error "Cannot generate strings of negative length!"
  0 -> do { return $ (ts, if makesEpsilon then (Just "") else Nothing) }
  n -> g s n ts
  where
    f :: NonTerm -> Int -> State Tables (M.Map [Sym] Integer)
    f nt n = do
      ts <- get
      case (M.lookup (nt, n) (ft ts)) of
        Just ns -> return ns
        Nothing -> do
            res <- (fmap M.fromList $ mapM (\k -> do { v <- fp (nt, k) 0 n ; return (k, sum v) }) (m_lookup nt rs))
            v <- get
            put $ v { ft = (M.insert (nt, n) res (ft v)) }
            return res
    fp :: Rule -> Int -> Int -> State Tables [Integer]
    fp r k n = do
      ts <- get
      case (M.lookup (r, k, n) (fpt ts)) of
        _ | (n == 0 || k >= length (snd r)) -> return []
        Just ns -> return ns
        Nothing -> do
          let x = (snd r) !! k -- why isn't !! safe? the world may never know.
          let tij = length (snd r) - 1
          res <- case x of {
            Left _  | ((k == tij) && (n == 1)) -> return [1] -- paper has n==0, but that's gotta be a typo
                    | k == tij  -> return [0]
                    | otherwise -> do {
                        t <- fp r (k+1) (n-1);
                        return [sum t] } ;
            Right y | k == tij -> do {
                        t <- f y n;
                        return [sum t] }
                    | otherwise -> mapM (\l -> do {
                        a <- f y l ;
                        b <- fp r (k+1) (n-l) ;
                        return $ sum a * sum b ;
                      }) [1..(n-tij+k)] }
          v <- get
          put $ v { fpt = (M.insert (r, k, n) res (fpt v)) }
          return res

    g :: RandomGen r => NonTerm -> Int -> Tables -> State r (Tables, Maybe String) -- it would be nice for tables to also be in state here, but that's hairy.
    g nt n ts = do
      let p = runState (f nt n) ts
      mr <- choose (M.assocs $ fst p)
      case mr of {
        Nothing -> return $ (snd p, Nothing) ;
        Just r -> gp (nt, r) 0 n (snd p) }

    gp :: RandomGen r => Rule -> Int -> Int -> Tables -> State r (Tables, Maybe String)
    gp r k n ts = do
      let x = (snd r) !! k -- todo fix lack of safety, though it maybe is not needed
      let tij = length (snd r) - 1
      case x of {
        Left (Term c) | k == tij  -> return (ts, Just [c])
                    | otherwise -> do { rv <- gp r (k+1) (n-1) ts ; return $ (fst rv, case (snd rv) of { Just z -> Just ([c] ++ z) ; Nothing -> Nothing }) } ;
        Right nt    | k == tij  -> g nt n ts
                    | otherwise -> let p = runState (fp r k n) ts in do { -- I want to know why I can't inline the let p, but...
                        ml <- choose (zip [0..] (fst p)) ;
                        case ml of {
                          Nothing -> return $ (snd p, Nothing) ;
                          Just l  -> do {
                            o1p <- g nt (l+1) (snd p) ;
                            o2p <- gp r (k+1) (n-(l+1)) (fst o1p) ;
                            return $ (fst o2p, case (snd o1p, snd o2p) of {
                              (Just x, Just y) -> Just (x ++ y) ;
                              _                -> Nothing
                            })
                          }
                        }
                      }
      }

-- Convencience version of generate which uses the globl RNG.
generate :: DenulledGrammar -> Tables -> Int -> IO (Tables, Maybe String)
generate g t n = do
  r <- getStdGen
  let p = runState (generateDet g t n) r
  setStdGen (snd p)
  return $ fst p

-- Generate a list of Maybe Strings. Does not take or return the side tables; if you want those, use generate directly.
generateMany :: DenulledGrammar -> Int -> Int -> IO [Maybe String]
generateMany g l n = do
  a <- foldM f (emptyTables, []) [1..n]
  return $ snd a
  where
    f acc x = do
      v <- generate g (fst acc) l
      case v of (t, r) -> return (t, r:(snd acc))


emptyTables = Tables { ft = M.empty, fpt = M.empty }

 -- Choose a random item from a list with weights, with the probability of choosing a given index being proportional to the weight
choose :: RandomGen r => [(a, Integer)] -> State r (Maybe a)
choose l = do
  ra <- get
  let total = sum $ fmap snd l
  let p = randomR (0, total-1) ra
  put $ snd p
  let v = fst p
  return $ case total of {
    0 -> Nothing ;
    n -> snd $ foldl (\ap xp -> case ap of {
        (c, Nothing) | v < c + (snd xp) -> (0, Just (fst xp))
                     | otherwise        -> (c+(snd xp), Nothing) ;
        o -> o
      }) (0, Nothing) l }






---------------- Parsing ----------------


-- Basically a not-necessarily-complete parse. 
data EarleyState = EState { rule :: Rule, startIndex :: Int, children :: [Maybe EarleyState] } deriving (Show, Eq)

type Chart = M.Map Int [EarleyState]

-- Returns all of the parse trees for that string. Can go into an infinite loop if there are infinitely many. TODO use selfDeriving to avoid that.
-- todo a version of this which only produces at most one / at most two parses.
parse :: Grammar -> String -> [EarleyState]
parse (Grammar (st, rs)) str =
  let gamma = (NonTerm "GAMMA", [Right st]) -- TODO give this a better, unique name
      chart = m_insert 0 (EState {rule = gamma, startIndex = 0, children = []}) M.empty in
    fmap (fromJust . head . children) $ filter (\s -> rule s == gamma) $ m_lookup (length str) (foldl outer chart [0..(length str)])
  where
    outer :: Chart -> Int -> Chart
    outer c i = modifying_fold inner c 0
      where
        inner :: Chart -> EarleyState -> Chart
        inner c s
          | done s = complete c s i
          | otherwise = case (next s) of
              Left t -> scan c s i t
              Right nt -> predict c s i nt

        modifying_fold :: (Chart -> EarleyState -> Chart) -> Chart -> Int -> Chart -- todo abstract or find existing abstraction, or refactor (possibly doing away with charts entirely)
        modifying_fold f c' n = case (drop n $ m_lookup i c') of
          []  -> c'
          e:_ -> modifying_fold f (f c' e) (n+1)

    next :: EarleyState -> Sym
    next s = (snd (rule s)) !! (length (children s))

    done :: EarleyState -> Bool
    done s = length (children s) == length (snd (rule s))

    scan :: Chart -> EarleyState -> Int -> Term -> Chart
    scan c s i t = if (i < length str) && (t == Term (str !! i)) then c' else c
      where c' = m_nodup_append (i+1) (EState {rule = rule s, startIndex = startIndex s, children = (children s) ++ [Nothing]}) c

    predict :: Chart -> EarleyState -> Int -> NonTerm -> Chart
    predict c s i nt = redo $ foldl go c (m_lookup nt rs)
      where
        go :: Chart -> [Sym] -> Chart
        go a prod = m_nodup_append i (EState {rule = (nt, prod), startIndex = i, children = []}) a

        redo :: Chart -> Chart -- handle silly nullable cornercase: might need to "re-run" completer for a nullable if we are predicting that nullable
        redo c = foldl rego c (filter f $ m_lookup i c)

        f cand = (nt == fst (rule cand)) && (i == startIndex cand) && (done cand) 
        rego a cand = m_nodup_append i (EState { rule = rule s, startIndex = startIndex s, children = children s ++ [Just cand]}) a

    complete :: Chart -> EarleyState -> Int -> Chart
    complete c s i = foldl go c (filter f $ m_lookup (startIndex s) c)
      where
        f s' = (not (done s')) && (Right (fst (rule s)) == next s')
        go a p = m_nodup_append i (EState {rule = rule p, startIndex = startIndex p, children = children p ++ [Just s]}) a


-- Transform a raw parse tree into the form of your choosing.
-- The list passed to the provided function will have one item for each nonterminal in the RHS of the rule, in order. 
evalParse :: (Rule -> [a] -> a) -> EarleyState -> a
evalParse f s = f (rule s) (fmap (evalParse f) (catMaybes (children s)))

