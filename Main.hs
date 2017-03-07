module Main where

import RLang

--main = getContents >>= print.interpret.calc.lexer


fibAndPlus :: String
fibAndPlus =    let x = (Var 'x')
                    y = (Var 'y')
                    z = (Var 'Z')
                    u = (Var 'u')
                    utX = (Con "unaryTuple" [x])
                    dupx = (DupEq utX)
                    x' = (Var 'c')
                    u' = (Var 'v')
                    su = (Con "S" [u])
                    su' = (Con "S" [u'])
                    pairXY = (Con "o" [x,y])
                    szVal = (ConsVal "S" [(LVal z)])

                    ----plus
                    pairXU = (Con "binaryTuple" [x,u])
                    pairXU2 = (Con "binaryTuple" [x',u'])
                    pairXSU = (Con "binaryTuple" [x',su'])
                    e1Plus = (LeftExp dupx)
                    e2Plus = (LetExp pairXU2 "plus" pairXU (LeftExp pairXSU))
                    casePlus = (CaseExp y [(z,e1Plus),(su,e2Plus)])

                    plus = (FunExp "plus" pairXY)
                    defPlus = (Def "plus" pairXY casePlus)
                    ------------------
                    ----fib
                    n = (Var 'n')
                    
                    m = (Var 'm')
                    sz = (Con "S" [z])
                    sm = (Con "S" [m])
                    l = (Var 'l')
                    pairSZ = (Con "binaryTuple" [sz,sz])
            
                    e1 = (LeftExp pairSZ)
                    e3 = (LetExp l "plus" pairXY (LeftExp l))
                    e2 = (LetExp pairXY "fib" m e3)
                    case1 = (CaseExp n [(z,e1),(sm,e2)])

                    ---Sigmas e Q
                    
                    sig = [('x',szVal),('y',szVal)]
                    sig' = []
                    q = [(defPlus,"plus")]
                in ("plus s[Z],S[Z] by function " ++ show defPlus ++ " \n") ++
                        ("Evaluates to: " ++ show (opSemantics sig sig' q plus)) ++ "\n" 



incRinc :: String
incRinc =           let x = (Var 'x')
                        y = (Var 'y')
                        z = (Var 'Z')
                        n = (Var 'n')
                        m = (Var 'm')
                        sz = (Con "S" [(Var 'Z')])
                        sn = (Con "S" [(Var 'n')])
                        sm = (Con "S" [(Var 'm')])
                        szVal = (ConsVal "S" [(LVal z)])
                        e1 = (LeftExp sz)
                        e2 = (LetExp m "inc" n (LeftExp sm)) -- Temp
                        eF = (CaseExp y [(z,e1),(sn,e2)])
                        incF = (FunExp "inc" y)
                        defInc = (Def "inc" y eF)
                        sig = [('y',szVal),('x',szVal)]
                        sig' = []
                        eRF = (RLet x "inc" y (LeftExp y))
                        rIncF = (FunExp "rinc" x)
                        defRInc = (Def "rinc" x eRF)
                        q = [(defInc,"inc"),(defRInc,"rinc")]
                    in  
                        ("Inc S(Z) by function " ++ show defInc ++ " \n") ++
                            ("Evaluates to: " ++ show (opSemantics sig sig' q incF)) ++ "\n" ++
                                ("rInc S[Z] by reverse function " ++ show defRInc)  ++ "\n" ++
                                    ("Evaluates to: " ++ show (opSemantics sig sig' q rIncF)) ++ "\n" 
                        {-print ("Inc S(Z) by function " ++ show defInc)
                        print ("Evaluates to: " ++ show (opSemantics sig sig' q incF))
                        print ("rInc S[Z] by reverse function " ++ show defRInc)
                        print ("Evaluates to: " ++ show (opSemantics sig sig' q rIncF))
-}
main =  do
            putStr incRinc
            putStrLn ("---.---.---.---.---.---.---.---.---.---")