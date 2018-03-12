module Main where

import RLang
import Examples
--main = getContents >>= print.interpret.calc.lexer


main =  do
            putStr incTest
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStr rIncTest
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStr plusTest
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStr rPlusTest
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStr fibTest
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStr rFibTest
