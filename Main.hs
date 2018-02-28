module Main where

import RLang

--main = getContents >>= print.interpret.calc.lexer

-- Construindo as funções a serem testadas utilizando os datatypes definidos em RLang.hs
fibAndPlus :: String
fibAndPlus =    let x = (Var 'x')
                    y = (Var 'y')
                    z = (Con "Z" [])
                    u = (Var 'u')
                    utX = (Con "unaryTuple" [x])
                    dupx = (DupEq utX)
                    x' = (Var 'c')
                    u' = (Var 'v')
                    su = (Con "S" [u])
                    su' = (Con "S" [u'])
                    pairXY = (Con "binaryTuple" [x,y])
                    zVal = (ConsVal "Z" [])
                    szVal = (ConsVal "S" [zVal])
                    sszVal = (ConsVal "S" [szVal])
                    ssszVal = (ConsVal "S" [sszVal])
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
                    pairYX = (Con "binaryTuple" [y,x])

                    e1 = (LeftExp pairSZ)
                    e3 = (LetExp l "plus" pairYX (LeftExp l))
                    e2 = (LetExp pairXY "fib" m e3)
                    case1 = (CaseExp n [(z,e1),(sm,e2)])

                    fib = (FunExp "fib" n)
                    defFib = (Def "fib" n case1)

                    ------------------- PLUS-1
                    k = (Var 'k')
                    j = (Var 'j')
                    pairKJ = (Con "binaryTuple" [k,j])
                    w = (Var 'w')
                    c = (Var 'c')
                    pairWQ = (Con "binaryTuple" [w,c])
                    eRP = (RLet pairKJ "plus" pairWQ (LeftExp pairWQ))
                    rplus =(FunExp "rplus" pairKJ)
                    defRPlus = (Def "rplus" pairKJ eRP)

                    ---------------------- fib-1
                    p = (Var 'p')
                    o = (Var 'o')
                    g = (Var 'g')
                    pairPO = (Con "binaryTuple" [p,o])
                    rLetFib = (RLet pairPO "fib" g (LeftExp g))
                    rFib = (FunExp "rfib" pairPO)
                    defRFib = (Def "rfib" pairPO rLetFib)
                    pVal = sszVal
                    oVal = ssszVal
                     ---Sigmas e Q

                    sig = [('x',szVal),('y',zVal)]
                    sig2 = [('x',szVal),('y',szVal)]
                    sig3 = [('k',szVal),('j',szVal)]
                    sig4 = [('k',sszVal),('j',ssszVal)]
                    sig' = []
                    sigFib = [('n',zVal)]
                    sigFib2 = [('n',sszVal)]
                    sigRFib = [('p',pVal),('o',oVal)]
                    q = [(defPlus,"plus"),(defRPlus,"rplus"),(defFib,"fib"),(defRFib,"rfib")]

                in ("plus s[Z],Z by function " ++ show defPlus ++ " \n")
                         ++ ("Evaluates to: " ++ show (opSemantics sig sig' q plus)) ++ "\n\n\n"
                          ++ ("plus s[Z],S[Z] by function " ++ show defPlus ++ " \n")
                                ++ ("Evaluates to: " ++ show (opSemantics sig2 sig' q plus)) ++ "\n\n"
                                   ++ ("rPlus " ++ show (snd (sig3!!0)) ++ "," ++ show (snd (sig3!!1)) ++ " by function " ++ show defRPlus ++ " \n")
                                        ++("Evaluates to: " ++ show (opSemantics sig3 sig' q rplus)) ++ "\n\n\n"
                                            ++ ("rPlus " ++ show (snd (sig4!!0)) ++ "," ++ show (snd (sig4!!1)) ++ " by function " ++ show defRPlus ++ " \n")
                                                ++ ("Evaluates to: " ++ show (opSemantics sig4 sig' q rplus)) ++ "\n\n\n"
                                                    ++ ( "fib Z by function " ++ show defFib) ++ "\n"
                                                       ++ ("Evaluates to: " ++ show (opSemantics sigFib sig' q fib)) ++ "\n\n"
                                                           ++ ( "fib S[S[Z]] by function " ++ show defFib) ++ "\n"
                                                                ++ ("Evaluates to: " ++ show (opSemantics sigFib2 sig' q fib)) ++ "\n\n"
                                                                    ++ ( "rfib "++ show pVal ++","++ show oVal ++" by function " ++ show defRFib) ++ "\n"
                                                                         ++ ("Evaluates to: " ++ show (opSemantics sigRFib sig' q rFib))

incRinc :: String
incRinc =           let x = (Var 'x') -- RInc x
                        y = (Var 'y') -- Inc y
                        z = (Con "Z" [])
                        n = (Var 'n')
                        m = (Var 'm')
                        sz = (Con "S" [z])
                        sn = (Con "S" [(Var 'n')])
                        sm = (Con "S" [(Var 'm')])
                        yVal = (ConsVal "S" [(ConsVal "Z" [])])
                        sssz = (ConsVal "S" [(ConsVal "S" [yVal])])
                        xVal = sssz -- (ConsVal "S" [yVal])

                        e1 = (LeftExp sz)
                        e2 = (LetExp m "inc" n (LeftExp sm)) -- Temp
                        eF = (CaseExp y [(z,e1),(sn,e2)])
                        incF = (FunExp "inc" y)
                        defInc = (Def "inc" y eF)
                        sig = [('y',yVal),('x',xVal)]
                        sig' = []
                        eRF = (RLet x "inc" y (LeftExp y))
                        rIncF = (FunExp "rinc" x)
                        defRInc = (Def "rinc" x eRF)
                        q = [(defInc,"inc"),(defRInc,"rinc")]
                    in
                        ("Inc " ++ show yVal ++ " by function " ++ show defInc ++ " \n") ++
                            ("Evaluates to: " ++ show (opSemantics sig sig' q incF)) ++ "\n\n\n" ++
                                ("rInc " ++ show xVal ++ " by reverse function " ++ show defRInc)  ++ "\n" ++
                                    ("Evaluates to: " ++ show (opSemantics sig sig' q rIncF)) ++ "\n"
                        {-print ("Inc S(Z) by function " ++ show defInc)
                        print ("Evaluates to: " ++ show (opSemantics sig sig' q incF))
                        print ("rInc S[Z] by reverse function " ++ show defRInc)
                        print ("Evaluates to: " ++ show (opSemantics sig sig' q rIncF))
-}

main =  do
            putStr incRinc
            putStrLn ("---.---.---.---.---.---.---.---.---.---")
            putStrLn fibAndPlus
