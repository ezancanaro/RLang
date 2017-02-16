module Main where

import RLang

--main = getContents >>= print.interpret.calc.lexer

main = let x = (Var 'x') in 
    print (rMatch (LVal x) (Var 'y') [])