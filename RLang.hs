module RLang where 
import Debug.Trace

doDebug = False
debug a b = if doDebug then trace a b else b

type Q = [(D,String)]

data L =  Var Char --Variáveis poderiam ser strings, mudar.
        | Con String [L]  
        | DupEq L -- Duplication = unaryTuple(L) | Equality = binaryTuple(L,L).-.-.-. Enforce on semantics translation!
                  -- Obrigando L a ser um Con, tupla unária ou binária. A sintaxe pode permitir as demais, mas será traduzida para tupla.
        deriving(Eq)

data DE = Dup L      -- Não está sendo usado.
        | Eq (L,L)
        deriving(Show, Eq)

data E =  LeftExp L
        | LetExp L String L E
        | RLet L String L E
        | CaseExp L [(L,E)] 
        | FunExp String L
        deriving(Eq)

data D = Def String L E
        deriving(Eq)

data Value =  LVal L
            | ConsVal String [Value]
            | DupVal Value
            | EqVal (Value,Value)
            | ErrorVal Char 
        deriving(Eq)

-- Instâncias de show para exibir os dataTypes de maneira mais limpa
instance Show (L) where
  show (Var c) = [c]
  show (Con c llist) = c ++ (show llist) 
  show (DupEq l) = "<" ++ (show l) ++">"

instance Show (Value) where
  show (LVal v) = (show v)
  show (DupVal v) = (show v)
  show (EqVal vpair) = (show vpair)
  show (ConsVal c vl) = c ++ (show vl)
  show (ErrorVal c) = [c]

instance Show (E) where
  show (LeftExp l) = show l
  show (LetExp l s l' e) = "let " ++ show l ++ " = " ++ s ++ " " ++ show l' ++ " in " ++ show e
  show (RLet l s l' e) = "rlet " ++ show l ++ " = " ++ s ++ " " ++ show l' ++ " in " ++ show e
  show (CaseExp l listLE) = "case " ++ show l ++ " of \n\t" ++ showCases listLE
  show (FunExp s l) = s ++ show l

instance Show (D) where
  show (Def s l e) = s ++ " " ++ show l ++ " =^= " ++ show e

type SigmaL = (Char,Value)
type Sigma = [SigmaL]
type DisjointSigma = [(Sigma,Char)]        

showCases :: [(L,E)] -> String -- Helper for Show instance
showCases [] = []
showCases (x:xs) = show x ++ "\n\t" ++ showCases xs



dupEquality :: DE -> DE -- Unused.
dupEquality (Dup l) = Eq (l,l)
dupEquality (Eq pair) = if ((fst pair) == (snd pair)) then (Dup (fst pair))
                            else (Eq pair)


duplicationOrEquality :: L -> (String,[L]) -- Determinar se preciso duplicar ou equalizar a left-expression.
duplicationOrEquality (Con s list) = case s of
                                              "unaryTuple" -> ("duplicate",list)
                                              "binaryTuple" -> ("equalize",list)
duplicationOrEquality _ = error "DupEq doesnt have a tuple in it."

equals :: Value -> Bool -- Testar a igualdade das left-exps nas tuplas de DupEq. 
equals (ConsVal "binaryTuple" list) = if ((head list) == (head (tail list))) then True
                                                        else False
equals _ = error "called equals on not a binaryTuple" -- 

extractValueFromConsVal :: Value -> Value -- Extrai o primeiro valor de uma tupla binária. Usado para equalizar.
extractValueFromConsVal (ConsVal "binaryTuple" listVal) = head listVal
extractValueFromConsVal _ = error "Trying to extract value from a not ConsVal v."

dupEqVal :: Value -> Value
dupEqVal (DupVal v) = EqVal (v,v)
dupEqVal (EqVal pairV) = if ((fst pairV) == (snd pairV)) then (DupVal (fst pairV))
                            else (EqVal pairV)


sigmaSubs :: L -> Value -> (Char,Value) -- Constrói a substituição var->val armazenada em um sigma.
sigmaSubs (Var x) v = (x,v)
sigmaSubs _ _ = error "Applying sigmaSubs to Non Variable Left-Expression"

rMatch :: Value -> L -> Sigma -> Sigma -- Regras para o "most-general-matcher" da linguagem. 
                                        --Obtenho uma substituição sigma com base em um valor e uma left-exp.
rMatch v (Var x) sig = debug ("rMatch:: v:" ++ show v ++ "<|" ++ show x)
                        extend (sig) (sigmaSubs (Var x) v) -- 
rMatch (ConsVal c vl) (Con c' ll) sig = if(c == c') then -- Confiro se o construtor com os valores equivale ao construtor com left-exps.
                                              debug ("rMatch::ConsVal->Con vl=" ++ show vl ++ " ll=" ++ show ll)
                                                sig ++ (rMatchOnCons vl ll) --Função auxiliar.
                                        else sig                                    
rMatch v (DupEq l) sig =  let duplicateOrEqualize = duplicationOrEquality l -- Determino se o operador requer duplicação ou equalização.
                              whatToDo = fst duplicateOrEqualize 
                              tuple = snd duplicateOrEqualize
                          in
                            case whatToDo of
                              "duplicate" -> debug ("rMatch DupEq duplicate")
                                              (let v' = ConsVal "binaryTuple" [v,v] in (rMatch v' l sig)) -- Duplico o valor e continuo a regra.
                              "equalize" -> debug ("rMatch DupEq equalize")
                                              (if equals v then 
                                                let v' = ConsVal "unaryTuple" [v] in (rMatch v' l sig) -- Caso sejam iguais, armazeno um só.
                                              else
                                                let v' = ConsVal "binaryTuple" [v,v] in (rMatch v' l sig)) -- Caso contrário, não altero os valores.
rMatch _ _ _ = [] --Não consegue match, retorna um sigma vazio



rMatchOnCons :: [Value] -> [L] -> Sigma -- Aplica as regras de RMatch a lista de left-exps e vals do construtor.
                                        -- Cada left-exp é associada a um valor.
rMatchOnCons [] [] = []
rMatchOnCons [] ll = [('&',ErrorVal 'e')] -- error "Values dont match lef-exps". Permite a continuação caso não haja match.
rMatchOnCons vl [] = [('&',ErrorVal 'e')] -- error "Left-exps dont match values". Permite a continuação caso não haja match.
rMatchOnCons vl ll = (rMatch (head vl) (head ll) []) ++ (rMatchOnCons (tail vl) (tail ll))

extend :: Sigma -> (Char, Value) -> Sigma -- Extende a lista de substituições sigma.
extend sig xv = xv : sig

--Retorna um valor através das regras de rMatch e de um sigma.
rMatchVal :: Sigma -> L -> Value -- O caminho inverso de RMatch, para recuperar um valor com base em um sigma existente.
rMatchVal sig (Var x) = let val' = [ val | (var,val) <- sig, var == x ] in if ( val' /= []) then (head val') -- Procuro um valor associado a var.
                                                                                      else error "No variable match in Sigma"
rMatchVal sig (Con c vl) =  ConsVal c (rMatchValCons sig vl) -- Construo um valor Cons através das left-exp do construtor.
rMatchVal sig (DupEq l) = let v' = debug("rMatchVal DupEq:: sig:" ++ show sig ++ " l:" ++ show l)
                                    rMatchVal sig l 
                              duplicateOrEqualize = duplicationOrEquality l
                              whatToDo = fst duplicateOrEqualize 
                          in
                            case whatToDo of -- Aplly to v' the inverse of whatToDo, since whatToDo represents what was done to get v'
                              "duplicate" ->  debug ("rMatchVal DupEq duplicate" ++ show sig)
                                                ConsVal "binaryTuple" [v',v']
                              "equalize" -> debug ("rMatchVal DupEq equalize" ++ show v') 
                                              ConsVal "binaryTuple" [v',v']

rMatchValCons :: Sigma -> [L] -> [Value] -- Auxiliar a rMatchVal, aplica rMatchVal as left-exps do construtor.
rMatchValCons sig [] = []
rMatchValCons sig vl = (rMatchVal sig (head vl)) : (rMatchValCons sig (tail vl))

getEfromD :: D -> E -- Extrai a expressão armazenada na definição de uma função.
getEfromD (Def _ _ e) = e

--OPERATIONAL SEMANTICS
opSemantics :: Sigma -> Sigma -> Q -> E -> Value -- Regras da semântica operacional da linguagem.
opSemantics sig _ q (LeftExp l) = (rMatchVal sig l) 

opSemantics sig _ q (FunExp f l ) = let def' = [ def | (def,name) <- q, name == f] in -- Verifico se a função foi declarada anteriormente.
                                                              if ( def' /= [])  then  let v'= (opSemantics sig [] q (LeftExp l)) 
                                                                    in  let sigf = (rMatch v' l [])--(rMatch v' lf []) 
                                                                        in (opSemantics sigf [] q (getEfromD (head def')))--(opSemantics sigf q ef)
                                                              else error ("opSemantics: FUNEXP -- function " ++ show f ++" not in Q")

opSemantics sigIn sigE q (LetExp lout f lin e) = let vout = (opSemantics sigIn [] q (FunExp f lin)) in 
                                                                                  let sigOut = (rMatch vout lout []) in
                                                                                      (opSemantics sigOut sigE q e)

opSemantics sigIn sigE q (RLet lin f lout e) = let vin = (rMatchVal sigIn lin)  in
                                                            let sigOut = debug ("vin = "++ show vin) 
                                                                          (reverseOpSemantics sigIn q (FunExp f lout) vin) 
                                                                      in
                                                                        debug ("sigOut = "++ show sigOut) 
                                                                          (opSemantics sigOut sigE q e)
--let vin = (opSemantics sigOut [] q (FunExp f lout)) in -- TO DO
  --                                                                          (opSemantics sigOut sigE q e)

opSemantics sigL sigT q (CaseExp l listLE) = let v' = (opSemantics sigL [] q (LeftExp l)) 
                                                 listL = getListL listLE in 
                                                      let sigAndJ = jOnCaseRule listL v' 0 in
                                                          let sigLJ = sigL ++ fst sigAndJ
                                                              j = snd sigAndJ in 
                                                                let ej = getEJ listLE j in 
                                                                    let v = (opSemantics sigLJ sigT q ej) in v
                                                         --Ainda devo testar o jOnCaseRule2, com as leaves.


--REVERSEChecking OPERATIONAL SEMANTICS
reverseOpSemantics :: Sigma -> Q -> E -> Value -> Sigma -- Semântica operacional na ordem inversa, aplicada pela semântica do rLet
                                                    -- Retorna uma substituição sigma, com base no valor de saída da função a ser invertida.
reverseOpSemantics sig q (LeftExp l) v = (rMatch v l sig) 

reverseOpSemantics sig q (FunExp f l) v = let def' = [ def | (def,name) <- q, name == f] in
                                                              if ( def' /= [])  then 
                                                                    let sigf = (reverseOpSemantics sig q (getEfromD (head def')) v) --(opSemantics sigf q ef)
                                                                      in let v' = (rMatchVal sigf l)--(rMatch v' lf []) 
                                                                        in debug ("sigF=" ++ show sigf ++ " v'=" ++ show v') 
                                                                                 (reverseOpSemantics sig q (LeftExp l) v')--
                                                              else error "opSemantics: FUNEXP -- function f not in Q"

reverseOpSemantics sigIn q (LetExp lout f lin e) v =   sigIn -- TO DO
                                                {-let vout = (opSemantics sigIn [] q (FunExp f lin)) in 
                                                                                  let sigOut = (rMatch vout lout []) in
                                                                                      (opSemantics sigOut sigE q e)
                                                -}
reverseOpSemantics sigIn q (RLet lin f lout e) v =     sigIn -- TO DO

                                                {-let vin = (rMatchVal sigIn lin) in
                                                            let sigOut = (reverseOpSemantics f lout vin) in
                                                                    (opSemantics sigOut sigE q e)
--let vin = (opSemantics sigOut [] q (FunExp f lout)) in -- TO DO
  --                                                                          (opSemantics sigOut sigE q e)
                                                -}
reverseOpSemantics sigL q (CaseExp l listLE) v = let listE = getListE listLE in 
                                                    let j = debug ("listLE=" ++ show listLE)
                                                              snd (jOnCaseRule2 listE v 0) in
                                                      let ej = getEJ listLE j in 
                                                        let sigL' = debug ("sigL=" ++ show sigL ++ " ej=" ++ show ej ++ " j=" ++ show j)
                                                                      (reverseOpSemantics sigL q ej v) in
                                                          let  listL = getListL listLE in 
                                                            let v2' = fst (jOnCaseRuleVal listL 0 sigL') in
                                                              debug ("sigL'=" ++ show sigL' ++ " v2'=" ++ show v2') 
                                                                (reverseOpSemantics sigL q (LeftExp l) v2')

                                              {-let v' = (opSemantics sigL [] q (LeftExp l)) 
                                                 listL = getListL listLE in 
                                                      let sigAndJ = jOnCaseRule listL v' 0 in
                                                          let sigLJ = fst sigAndJ
                                                              j = snd sigAndJ in 
                                                                let ej = getEJ listLE j in 
                                                                    let v = (opSemantics sigLJ sigT q ej) in v
                                                -}
                                                                  

getEJ :: [(L,E)] -> Int -> E -- Extrai uma expressão de uma dupla (left-exp,exp). Utilizada para a regra semântica do case.
getEJ [] i = error "No expressions in list (CaseExp)"
getEJ listLE i = snd (listLE !! i)

getListL :: [(L,E)] -> [L] -- Extrai uma lista com todas as left-exps de uma expressão case.
getListL [] = []
getListL listLE = fst (head listLE) : getListL (tail listLE)

getListE :: [(L,E)] -> [E] -- Extrai uma lista com todas as exps de uma expressão case.
getListE [] = []
getListE listLE = snd (head listLE) : getListE (tail listLE)

jOnCaseRule :: [L] -> Value -> Int -> (Sigma,Int) -- Parte da regra semântica do case, determina qual caso deve ser avaliado. 
                                          --Retorna uma substituição sigma e a posição do caso escolhido.
jOnCaseRule [] v' i = error "Couldnt match Val with any case in CaseExp"
jOnCaseRule listL v' i = let sigl = rMatch v' (head listL) [] in 
                                                if (sigl == []) then jOnCaseRule (tail listL) v' (i+1)
                                                else (sigl,i)

jOnCaseRuleVal :: [L] -> Int -> Sigma -> (Value,Int) --Última parte da regra semântica do case.
jOnCaseRuleVal [] _ _ = error "Case rule without list of Left-Expressions"
jOnCaseRuleVal listL j sig = let val = rMatchVal sig (head listL) in -- MUDAR rMatchVal para possibilitar testes
                                (val,j) 

--A posição do l da func jOnCaseRule deve ser a mesma posiçao desta func.
jOnCaseRule2 :: [E] -> Value -> Int -> (Sigma, Int)
jOnCaseRule2 [] v i = ([],-1)
jOnCaseRule2 listE v i = let leavesE = leaves(head listE) [] in 
                            let matchLeaf = debug("leavesE=" ++ show leavesE)
                                              jOnCaseRule2Match v leavesE in 
                                if (matchLeaf == []) then jOnCaseRule2 (tail listE) v (i+1)
                                else (matchLeaf,i)   

jOnCaseRule2Match :: Value -> [L] -> Sigma
jOnCaseRule2Match _ [] = []
jOnCaseRule2Match v leavesE = let match = debug ("jOnCaseMatch: v=" ++ show v ++ " l'=" ++ show (head leavesE))
                                            rMatch v (head leavesE) [] in
                                if(match == []) then jOnCaseRule2Match v (tail leavesE)
                                else match
 
--leaves(let l1=f l2 in e)=leaves(e) | leaves(rlet l1=f l2 in e)=leaves(e) | leaves(case l of {pi->ei})=Um-ileaves(ei) | leaves(l)={l}                               
leaves :: E -> [L] -> [L] -- Retorna uma lista com as left-exps folhas da árvore de derivação. Utililizada na semântica do case.
leaves (LetExp l1 f l2 e) leavesList = leaves e leavesList --As folhas de um let, são as folhas da exp no seu corpo.
leaves (CaseExp l listPE) leavesList = let ei = map extractEfromPair listPE --Extraio as exps do corpo dos casos.
                                            in leavesHelper ei leavesList -- As folhas do case é a união das folhas das exps no corpo.
leaves (RLet l1 f l2 e) leavesList = leaves e leavesList --As folhas de um rlet, são as folhas da exp no seu corpo.
leaves (LeftExp l) leavesList = l : leavesList -- Uma left-exp é uma folha.


leavesHelper :: [E] -> [L] -> [L] --Auxiliar para a lista de exps do case.
leavesHelper [] _ = []
leavesHelper listE leavesList = leaves (head listE) leavesList ++ leavesHelper (tail listE) leavesList

extractEfromPair :: (L,E) -> E
extractEfromPair le = snd le


{- 
  LEMMA 1:
    v<l -> σ => (σl)↓ = v ∧ ∀σ' . [(σ'l)↓ = v => Eσ''.σ' = σ \disjointUnion σ'']
    
  l avalia para v em sigma SE aplicando a substituição sigma em l, e aplicando os operadores de eq/dup
  no resultante, obtenho v. E para todo sig' que obtém v observando o anterior, existe um sig'' tal que
  sig' pode ser decomposto na união disjunta de sig e sig''.


-}