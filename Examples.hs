module Examples where
import RLang

y = (Var 'y') -- Inc y
x = (Var 'x') -- RInc x
pairXY = (Con "binaryTuple" [x,y])
z = (Con "Z" [])
zVal = (ConsVal "Z" [])
szVal = (ConsVal "S" [zVal])
sszVal = (ConsVal "S" [szVal])
ssszVal = (ConsVal "S" [sszVal])


intToValue :: Int -> Value
intToValue 0 = ConsVal "Z" []
intToValue x = ConsVal "S" [intToValue $ x-1]

intToL :: Int -> L
intToL 0 = Con "Z" []
intToL x = Con "S" [intToL $ x-1]

-- Construindo as funções a serem testadas utilizando os datatypes definidos em RLang.hs

-- exampleProg :: String
-- exampleProg = let (inc,defInc) = buildInc
--                   q = [(defInc,"inc")]


buildPlus :: D
buildPlus = let
                u = (Var 'u')
                utX = (Con "unaryTuple" [x])
                dupx = (DupEq utX)
                x' = (Var 'c')
                u' = (Var 'v')
                su = (Con "S" [u])
                su' = (Con "S" [u'])
                ----plus
                pairXU = (Con "binaryTuple" [x,u])
                pairXU2 = (Con "binaryTuple" [x',u'])
                pairXSU = (Con "binaryTuple" [x',su'])
                e1Plus = (LeftExp dupx)
                e2Plus = (LetExp pairXU2 "plus" pairXU (LeftExp pairXSU))
                casePlus = (CaseExp y [(z,e1Plus),(su,e2Plus)])
                plus = (FunExp "plus" pairXY)
                defPlus = (Def "plus" pairXY casePlus)
            in defPlus

plus :: L -> Q -> (Value,D)
plus l q' =   let defPlus = buildPlus
                  q = [(defPlus,"plus")] ++ q'
                  plusX = FunExp "plus" l
                  sig = []
              in (opSemantics sig [] q plusX, defPlus)


buildFib :: D
buildFib =  let n = (Var 'n')
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
            in  defFib

fib :: L -> Q -> (Value,D)
fib l q' = let   defFib = buildFib
                 q = [(defFib,"fib")] ++ q'
                 fibX = FunExp "fib" l
                 sig = []
            in  (opSemantics sig [] q fibX, defFib)

plusTest :: String
plusTest =  let
              l1 = intToL 1
              l2 = intToL 0
              l = (Con "binaryTuple" [l1,l2])
              q = []
              (evals,defPlus) = plus l q
            in ("plus " ++ show l1 ++ "," ++ show l2 ++ "by function " ++ show defPlus ++ " \n")
                  ++ ("Evaluates to: " ++ show evals) ++ "\n\n\n"

fibTest :: String
fibTest = let l = intToL 0
              defPlus = buildPlus
              q = [(defPlus,"plus")]
              (evals,defFib) = fib l q
          in  ("fib " ++ show l ++ " by function " ++ show defFib) ++ "\n"
                ++ ("Evaluates to: " ++ show evals) ++ "\n\n"


buildRPlus :: D
buildRPlus = let  k = (Var 'k')
                  j = (Var 'j')
                  pairKJ = (Con "binaryTuple" [k,j])
                  w = (Var 'w')
                  c = (Var 'c')
                  pairWQ = (Con "binaryTuple" [w,c])
                  eRP = (RLet pairKJ "plus" pairWQ (LeftExp pairWQ))
                  rplus =(FunExp "rplus" pairKJ)
                  defRPlus = (Def "rplus" pairKJ eRP)
              in  defRPlus


buildRFib :: D
buildRFib = let p = (Var 'p')
                o = (Var 'o')
                g = (Var 'g')
                pairPO = (Con "binaryTuple" [p,o])
                rLetFib = (RLet pairPO "fib" g (LeftExp g))
                rFib = (FunExp "rfib" pairPO)
                defRFib = (Def "rfib" pairPO rLetFib)
            in  defRFib

rPlus :: L -> Q -> (Value,D)
rPlus l q' =  let  defRPlus = buildRPlus
                   q = [(defRPlus,"rplus")] ++ q'
                   rPlusX = FunExp "rplus" l
                   sig = []
               in (opSemantics sig [] q rPlusX,defRPlus)

rFib :: L -> Q -> (Value,D)
rFib l q' = let   defRFib = buildRFib
                  q = [(defRFib,"rfib")] ++ q'
                  rFibX = FunExp "rfib" l
                  sig = []
               in (opSemantics sig [] q rFibX,defRFib)


rPlusTest :: String
rPlusTest = let l1 = intToL 1
                l2 = intToL 1
                l = (Con "binaryTuple" [l1,l2])

                defPlus = buildPlus
                q = [(defPlus,"plus")]
                (evals,defRPlus) = rPlus l q
            in ("rPlus " ++ show l1 ++ "," ++ show l2 ++ " by function " ++ show defRPlus ++ " \n")
                 ++ ("Evaluates to: " ++ show evals) ++ "\n\n\n"

rFibTest :: String
rFibTest = let l1 = intToL 2
               l2 = intToL 3
               l = (Con "binaryTuple" [l1,l2])
               defFib = buildFib
               defPlus = buildPlus
               q = [(defFib,"fib"),(defPlus,"plus")]
               (evals,defRFib) = rFib l q
           in ( "rfib "++ show l1 ++","++ show l2 ++" by function " ++ show defRFib) ++ "\n"
                    ++ ("Evaluates to: " ++ show evals) ++ "\n\n\n"


buildInc :: D
buildInc =          let
                        z = (Con "Z" [])
                        n = (Var 'n')
                        m = (Var 'm')
                        sz = (Con "S" [z])
                        sn = (Con "S" [(Var 'n')])
                        sm = (Con "S" [(Var 'm')])
                        yVal = (ConsVal "S" [(ConsVal "Z" [])])

                        e1 = (LeftExp sz)
                        e2 = (LetExp m "inc" n (LeftExp sm)) -- Temp
                        eF = (CaseExp y [(z,e1),(sn,e2)])
                        incF = (FunExp "inc" y)
                        defInc = (Def "inc" y eF)
                        in defInc


inc :: L -> Q -> (Value,D)
inc l q' = let   defInc = buildInc
                 q = [(defInc,"inc")] ++ q'
            --in (opSemantics sig [] q incF, defInc)
                 incX = FunExp "inc" l
              in (opSemantics [] [] q incX, defInc)


buildRinc :: D
buildRinc = let eRF = (RLet x "inc" y (LeftExp y))
                rIncF = (FunExp "rinc" x)
                defRInc = (Def "rinc" x eRF)
            in defRInc

rInc :: L -> Q -> (Value,D)
rInc l q' = let   defRInc = buildRinc
                  sig = []
                  q = [(defRInc,"rinc")] ++ q'
                  rIncX = FunExp "rinc" l
              in (opSemantics sig [] q rIncX,defRInc)

incTest :: String
incTest = let
              l = intToL 1
              q = []
              (evals,defInc) = inc l q
          in
              ("Inc " ++ show l ++ " by function " ++ show defInc ++ " \n") ++
                ("Evaluates to: " ++ show (evals)) ++ "\n\n\n"

rIncTest :: String
rIncTest = let
               l = intToL 3
               defInc = buildInc
               q = [(defInc,"inc")]
               (evals,defRInc) = rInc l q
            in ("rInc " ++ show l ++ " by reverse function " ++ show defRInc)  ++ "\n" ++
                  ("Evaluates to: " ++ show (evals)) ++ "\n"
