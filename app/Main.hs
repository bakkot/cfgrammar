module Main where

import CFGrammar
import Data.Maybe (catMaybes)


plus  = (NonTerm "E", [nonterm "T", term '+', nonterm "E"])
e_t   = (NonTerm "E", [nonterm "T"])
times = (NonTerm "T", [nonterm "F", term '*', nonterm "T"])
t_f   = (NonTerm "T", [nonterm "F"])
paren = (NonTerm "F", [term '(', nonterm "E", term ')'])
f_n   = (NonTerm "F", [nonterm "N"])
one   = (NonTerm "N", [term '1'])
two   = (NonTerm "N", [term '2'])
three = (NonTerm "N", [term '3'])

math :: Grammar
math = fromRules [plus, e_t, times, t_f, paren, f_n, one, two, three]

evalMath :: Rule -> [Int] -> Int
evalMath r xs
  | r == plus  = sum xs
  | r == times = product xs
  | r == one   = 1
  | r == two   = 2
  | r == three = 3
  | otherwise  = head xs


main :: IO ()
main = do
  let smath = prepare math
  vs <- generateMany smath 21 10000
  let vsp = fmap (\v -> evalParse evalMath $ head $ parse math v) (catMaybes vs)
  putStrLn $ show vsp

