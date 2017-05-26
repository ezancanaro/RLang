module RLang where 
import Debug.Trace

doDebug = False

debug a b = if doDebug then trace a b else b

type Q = [(D,String)]

data L =  Var Char --Single Char variables.
        | Con String [L]  
        | DupEq L -- Duplication = unaryTuple(L) | Equality = binaryTuple(L,L).-.-.-. Enforce on semantics translation!
                  -- Forcing L to be a Con, unaryTuple or binaryTuple. Sintax may allow L to be a single var, but the parser should translate to tuple.
        deriving(Eq)

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
            | EqVal (Value,Value) -- Differentiating duplication and equality in the values.
            | ErrorVal Char -- Value to propagate non-terminating erros throughout evaluation.
        deriving(Eq)

-- Pretty printing
instance Show (L) where
  show (Var c) = [c]
  show (Con "unaryTuple" llist) = "<" ++ show (head llist) ++ ">"
  show (Con "binaryTuple" llist) = "<" ++ show (head llist)++ "," ++ show (head (tail llist)) ++ ">" 
  show (Con c llist) = c ++ (show llist) 
  show (DupEq l) = "|" ++ (show l) ++"|"

instance Show (Value) where
  show (LVal v) = (show v)
  show (DupVal v) = "|" ++ (show v) ++ "|"
  show (EqVal vpair) = (show vpair)
  show (ConsVal "unaryTuple" vl) = "<" ++ show (head vl) ++ ">"
  show (ConsVal "binaryTuple" vl) = "<" ++ show (head vl) ++ "," ++ show (head (tail vl)) ++ ">"
  show (ConsVal c vl) = c ++ (show vl)
  show (ErrorVal 'm') = "[Error] " ++ "matching"
  show (ErrorVal 'e') = "[Error]" ++ "consMatcher"
  show (ErrorVal c) = "[Error]" ++ [c]

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


duplicationOrEquality :: L -> (String,[L]) -- Determine if the L in a duplication/equality operator must be duplicated or equalized.
duplicationOrEquality (Con s list) = case s of
                                              "unaryTuple" -> ("duplicate",list)
                                              "binaryTuple" -> ("equalize",list)
duplicationOrEquality _ = error "DupEq doesnt have a tuple in it."

equals :: [Value] -> Bool -- Test the equality of values in a binaryTuple from an eq val. 
equals list = if ((head list) == (head (tail list))) then True
                                                        else False
--equals _ = error "called equals on not a binaryTuple" -- 

extractValueFromConsVal :: Value -> Value -- Extracting first value from a binary tuple. Helper for equalizing.
extractValueFromConsVal (ConsVal "binaryTuple" listVal) = head listVal
extractValueFromConsVal _ = error "Trying to extract value from a not ConsVal v."

dupEqVal :: Value -> Value -- Unused function
dupEqVal (DupVal v) = EqVal (v,v)
dupEqVal (EqVal pairV) = if ((fst pairV) == (snd pairV)) then (DupVal (fst pairV))
                            else (EqVal pairV)

duplicateEqualizeOps :: Value -> Value -- Apply the duplication/equality operator on a value.
duplicateEqualizeOps (ConsVal "unaryTuple" [v]) = ConsVal "binaryTuple" [v,v]
duplicateEqualizeOps (ConsVal "binaryTuple" vals) = if equals vals then ConsVal "unaryTuple" [(head vals)]
                                                 else ErrorVal 'd'
duplicateEqualizeOps _ = ErrorVal 'd'

sigmaSubs :: L -> Value -> (Char,Value) -- Constructs the var->value substitution stored in a sigma.
sigmaSubs (Var x) v = (x,v)
sigmaSubs _ _ = error "Applying sigmaSubs to Non Variable Left-Expression"

rMatch :: Value -> L -> Sigma -> Sigma -- Implementation of the "most-general-matcher" rules. 
                                        --Returns a sigma based on a value and a left-expression.
                                        -- A sigma containing a ('&',ErrorVal Char) indicates a failed match.
rMatch v (Var x) sig = debug ("rMatch:: v:" ++ show v ++ "<|" ++ show x)
                        extend (sig) (sigmaSubs (Var x) v) -- Assign value to var.
rMatch v (DupEq l) sig = let v' = debug ("rMatch:DupEq-> v=" ++ show v ++ " l=" ++ show (DupEq l))
                                      duplicateEqualizeOps v in -- Apply the operator in the value supplied.
                                      if testVal v' then (rMatch v' l sig) --Test for problems in applying the operator
                                      else [('&',ErrorVal 'm')]
rMatch (ConsVal c vl) (Con c' ll) sig = if(c == c') then -- Check if the constructor in the left-exp is the same as the one in the value.
                                              debug ("rMatch::ConsVal->Con vl=" ++ show vl ++ " ll=" ++ show ll)
                                                sig ++ (rMatchOnCons vl ll) --Helper function-Applies rMatch to left-exps and vals inside the constructor.
                                        else debug ("rMatch::ConsVal-> ConsVal=" ++show c ++ " ConsLeftExp=" ++ show c')
                                              [('&',ErrorVal 'm')]                                    

rMatch _ _ _ = [('&',ErrorVal 'm')] --No match, returns an error.



rMatchOnCons :: [Value] -> [L] -> Sigma -- Applies rMatch to left-exps and vals inside the constructor.
                                        -- Each left-exp is assigned to one value.
rMatchOnCons [] [] = []
rMatchOnCons [] ll = [('&',ErrorVal 'e')] -- error "Values number dont match lef-exps".
rMatchOnCons vl [] = [('&',ErrorVal 'e')] -- error "Left-exps number dont match values".
rMatchOnCons vl ll = (rMatch (head vl) (head ll) []) ++ (rMatchOnCons (tail vl) (tail ll)) -- The actual evaluation

extend :: Sigma -> (Char, Value) -> Sigma -- Extends the sigma with a substitution.
extend sig xv = xv : sig

--Returns a value based on the rMatch rules, using a left-exp and a sigma.
rMatchVal :: Sigma -> L -> Value -- The inverse of rMatch.
rMatchVal sig (Var x) = let val' = [ val | (var,val) <- sig, var == x ] in if ( val' /= []) then debug("matched var " ++ show x ++ " val=" ++ show (head val'))
                                                                                                  (head val') -- Look for a value associated with a var.
                                                                                      else debug("rMatchVal:: non matching var=" ++ show x)
                                                                                            ErrorVal 'v'
rMatchVal sig (Con c vl) =let v' = debug("rMatchVal:: Cons c="++show c++" vl="++show vl ++ " sigma:" ++ show sig)   
                                    (rMatchValCons sig vl) in
                              if testVals v' then
                                  ConsVal c (v') -- Build a Cons value with the left-exp constructor.
                              else
                                  ErrorVal 'v'
rMatchVal sig (DupEq l) = let v' = debug("rMatchVal DupEq:: sig:" ++ show sig ++ " l:" ++ show l)
                                     eraseTupleCons (rMatchVal sig l) -- Avoid duplicating the tuple constructor in a duplication/equality operation.
                              duplicateOrEqualize = duplicationOrEquality l -- Determine operation
                              whatToDo = fst duplicateOrEqualize 
                          in
                            case whatToDo of -- Aplly to v' the inverse of the operation decided, since whatToDo represents what was done to get v'.
                              "duplicate" ->  debug ("rMatchVal DupEq duplicate v=" ++ show v' ++ " sig:" ++ show sig)
                                                ConsVal "unaryTuple" [v']
                              "equalize" -> debug ("rMatchVal DupEq equalize" ++ show v') 
                                              ConsVal "binaryTuple" [v',v']

eraseTupleCons :: Value -> Value -- Erasing the tuple construct.
eraseTupleCons (ConsVal "unaryTuple" vlist) = head vlist
eraseTupleCons v = v 

rMatchValCons :: Sigma -> [L] -> [Value] -- Helper function, apply rMatchVal to the Cons
rMatchValCons sig [] = []
rMatchValCons sig vl = let v' = rMatchVal sig (head vl) in
                          if testVal v' then
                              v' : (rMatchValCons sig (tail vl))
                          else [ErrorVal 'v']



getEfromD :: D -> E -- Extract the expression from the definition of a function.
getEfromD (Def _ _ e) = e

getLfromD :: D -> L -- Extract the lef-expression fro the definition of a function.
getLfromD (Def _ l _) = l

--OPERATIONAL SEMANTICS
opSemantics :: Sigma -> Sigma -> Q -> E -> Value -- Rules for the operational semantics of the language
opSemantics sig _ q (LeftExp l) = (rMatchVal sig l) 

opSemantics sig _ q (FunExp f l ) = let def' = [ def | (def,name) <- q, name == f] in -- Check if the funtion was declared in the program.
                                                              if ( def' /= [])  then  
                                                                let v'= debug("opFunExp:: " ++ show f ++ " Evaluating v'")
                                                                          (opSemantics sig [] q (LeftExp l)) 
                                                                    in let lf = (getLfromD (head def')) -- Extract the left-exp from the function def.
                                                                          in let sigf = (rMatch v' lf [])-- Evaluate the left-exp with the value v'.
                                                                              in debug("opFunExp::" ++ show f ++ " sigf="++show sigf++" v'="++show v'++" lf="++show lf)
                                                                                  (opSemantics sigf [] q (getEfromD (head def')))--(opSemantics sigf q ef)
                                                              else error ("opFunExp -- function " ++ show f ++" not in Q")

opSemantics sigIn sigE q (LetExp lout f lin e) = let vout = debug("opLetExp::lin=" ++ show lin)
                                                              (opSemantics sigIn [] q (FunExp f lin)) in  -- Evaluate the function at the binding.
                                                                                  let sigOut = (rMatch vout lout []) in -- Evaluate the output left-exp.
                                                                                      (opSemantics sigOut sigE q e) -- Evaluate the expression in the body of the let binding.

opSemantics sigIn sigE q (RLet lin f lout e) = let vin = (rMatchVal sigIn lin)  in -- Evaluate the value that is the result of the function f.
                                                            let sigOut = debug ("opRLet::vin = "++ show vin) 
                                                                          (reverseOpSemantics sigIn q (FunExp f lout) vin) -- Backwards evaluating of the function which gives the resulting vin.
                                                                      in
                                                                        debug ("opRLet::sigOut = "++ show sigOut) 
                                                                          (opSemantics sigOut sigE q e) --Evaluate the expression in the rlet binding.

opSemantics sigL sigT q (CaseExp l listLE) = let v' = (opSemantics sigL [] q (LeftExp l)) -- Evaluate the left-expression parameter of case. 
                                                 listL = getListL listLE in 
                                                      let sigAndJ = debug("opCase:: v'=" ++ show v' ++ " listL="++show listL)  
                                                                      jOnCaseRule listL v' 0 in -- Select the appropiate case.
                                                          let sigLJ = sigL ++ fst sigAndJ
                                                              j = snd sigAndJ in 
                                                                let ej = getEJ listLE j in -- Extract the expression from chosen case 
                                                                    let v = debug("opCase:: ej=" ++ show ej)
                                                                              (opSemantics sigLJ sigT q ej) in v -- Evaluate the expression in the chosen case.
                                                         --Ainda devo testar o jOnCaseRule2, com as leaves.


--REVERSEChecking OPERATIONAL SEMANTICS
reverseOpSemantics :: Sigma -> Q -> E -> Value -> Sigma -- Backwards computation of the operational semantics, called by the rLet expression.
                                                    --Returns a sigma substitution, based on the expected final value of the forwards computation.
reverseOpSemantics sig q (LeftExp l) v = (rMatch v l sig) -- Match a value and a left-expression

reverseOpSemantics sig q (FunExp f l) v = let def' = [ def | (def,name) <- q, name == f] in --Check that the function exists in program.
                                                              if ( def' /= [])  then 
                                                                    let sigf = debug("reverseOpFun:: "++ show f++" Evaluating expression resulting in v=" ++ show v)
                                                                                (reverseOpSemantics sig q (getEfromD (head def')) v) -- Backwards compute the expression in function body.
                                                                      in let lf = (getLfromD (head def'))
                                                                        in let v' = (rMatchVal sigf lf)--Get the value resulting from the backwards computation of the expression.
                                                                          in debug ("reverseOpFun:: " ++ show f ++ "sigF=" ++ show sigf ++ " v'=" ++ show v') 
                                                                                   (reverseOpSemantics sig q (LeftExp l) v')-- Backwards evaluation of the function input left-exp.
                                                              else error "opSemantics: FUNEXP -- function f not in Q"

reverseOpSemantics sigIn q (LetExp lout f lin e) v =    let sigOut = debug("reverseOpLet:: evaluating e=" ++ show e ++ " yielding v=" ++ show v)
                                                                      (reverseOpSemantics sigIn q e v) -- Backwards evaluation of the expression in body.
                                                          in let vOut = (rMatchVal sigOut lout) -- Get the value resulting from previous evaluation.
                                                            in (reverseOpSemantics sigIn q (FunExp f lin) vOut) -- Backwards evaluation of the function in body.
                                          
                                                
reverseOpSemantics sigIn q (RLet lin f lout e) v =    let sigOut = (reverseOpSemantics sigIn q e v) -- Backwards evaluation of the expression in body.
                                                        in let vin = (opSemantics sigIn [] q (FunExp f lout)) -- Evaluate the function forward.
                                                          in rMatch vin lin sigIn -- Match the value with the left-expression in the input.
                                               

reverseOpSemantics sigL q (CaseExp l listLE) v = let listE = getListE listLE in 
                                                    let j = debug ("reverseOpCase::listLE=" ++ show listLE)
                                                              snd (jOnCaseRule2 listE v 0) in -- Find the case which outputs the value supplied
                                                      let ej = getEJ listLE j in 
                                                        let sigL' = debug ("reverseOpCase::sigL=" ++ show sigL ++ " ej=" ++ show ej ++ " j=" ++ show j ++ " v=" ++ show v)
                                                                      (reverseOpSemantics sigL q ej v) in -- Evaluate the expression in that case.
                                                          let  listL = getListL listLE in 
                                                            let v2'j = debug ("reverseOpCase::getting v' sigL'=" ++ show sigL' ++ " listL=" ++ show listL) 
                                                                          (jOnCaseRuleVal listL j sigL') -- Evaluate the left-exp from chosen case.
                                                                v2' = fst v2'j
                                                                jj = snd v2'j 
                                                              in
                                                                let j2 = snd(jOnCaseRule listL v2' 0) in -- Verify simmetrical first-match policy rule.
                                                                  if(j == j2) then
                                                                    debug ("reverseOpCase::sigL'=" ++ show sigL' ++ " v'=" ++ show v2' ++ " j=" ++ show j2) 
                                                                      (reverseOpSemantics sigL' q (LeftExp l) v2') -- Evaluate the left-exp in the case body.
                                                                  else
                                                                      error ("Symmetric first-match policy violated!")

                                                                  

getEJ :: [(L,E)] -> Int -> E -- Extracts the expression from a (L,E) pair stored in a Case expression.
getEJ [] i = error "No expressions in list (CaseExp)"
getEJ listLE i = snd (listLE !! i)

getListL :: [(L,E)] -> [L] -- Extract a list of all the cases in a Case expression.
getListL [] = []
getListL listLE = fst (head listLE) : getListL (tail listLE)

getListE :: [(L,E)] -> [E] -- Extract a list of all expressions in cases of a Case expression.
getListE [] = []
getListE listLE = snd (head listLE) : getListE (tail listLE)

getLAt :: [L] -> Int -> L -- Get a specified case from a Case expression.
getLAt list x = list!!x
--getLAt [] _ = error "Trying to get left-exp from empty list"


jOnCaseRule :: [L] -> Value -> Int -> (Sigma,Int) -- From the Case semantic rule, chooses wich case should be evaluated. 
                                          --Returns a sigma with the evaluation and the position of the chosen case.
jOnCaseRule [] v' i = error "Couldnt match Val with any case in CaseExp"
jOnCaseRule listL v' i = let sigl = debug ("jOnCaseRule:: v'=" ++ show v' ++ " l=" ++ show (head listL))
                                      rMatch v' (head listL) [] in 
                                                if (not (testSigs sigl)) then jOnCaseRule (tail listL) v' (i+1)
                                                else (sigl,i)

jOnCaseRuleVal :: [L] -> Int -> Sigma -> (Value,Int) --Última parte da regra semântica do case.
jOnCaseRuleVal [] _ _ = error "No adequate matching in Cases"
jOnCaseRuleVal listL j sig = let val = debug("jOnCaseRuleVal:: l= " ++ show (head listL) ++ " sig" ++ show sig)
                                        rMatchVal sig (listL!!j) in 
                                if testVal val then debug("jOnCaseRuleVal:: val=" ++ show val)
                                                      (val,j)
                                  else jOnCaseRuleVal (tail listL) (j+1) sig

--Test functions used to find errors in the evaluations, specially on failed matches.
testVal::Value -> Bool
testVal (ErrorVal v) = False
testVal _ = True 

testVals::[Value] -> Bool
testVals [] = True
testVals (vl) = let v = testVal (head vl) in
                  if (v) then testVals (tail vl)
                  else False

testSigs::Sigma -> Bool
testSigs [] = True
testSigs sig = let test = testSubs (head sig) in
                      if not(test) then test
                        else testSigs (tail sig)

testSubs::(Char,Value) -> Bool
testSubs (_,ErrorVal c) = False
testSubs _ = True

--Part of Case semantic rule, determines the chosen case in a backwards computation of the expression.
jOnCaseRule2 :: [E] -> Value -> Int -> (Sigma, Int)
jOnCaseRule2 [] v i = error ("Could not match value with any expression in Case. (Value doesn't arise from expression): " ++ show v)
jOnCaseRule2 listE v i = let leavesE = leaves(head listE) [] in 
                            let matchLeaf = debug("jOnCaseRule2::leavesE=" ++ show leavesE)
                                              jOnCaseRule2Match v leavesE in 
                                if (not (testSigs matchLeaf)) then jOnCaseRule2 (tail listE) v (i+1)
                                else (matchLeaf,i)   

jOnCaseRule2Match :: Value -> [L] -> Sigma -- Helper function for the previous one.
jOnCaseRule2Match _ [] = [('&',ErrorVal 'm')]
jOnCaseRule2Match v leavesE = let match = debug ("jOnCase2Match: v=" ++ show v ++ " l'=" ++ show (head leavesE))
                                            rMatch v (head leavesE) [] in
                                if(not (testSigs match)) then debug("jOnCase2Match:: no match")
                                                      jOnCaseRule2Match v (tail leavesE) 
                                else debug("jOnCase2Match:: matched: " ++ show match)
                                      match
 
--leaves(let l1=f l2 in e)=leaves(e) | leaves(rlet l1=f l2 in e)=leaves(e) | leaves(case l of {pi->ei})=Um-ileaves(ei) | leaves(l)={l}                               
leaves :: E -> [L] -> [L] -- Returns a list with all the leaf left-expression from the expressions in the case.
leaves (LetExp l1 f l2 e) leavesList = leaves e leavesList --Leaves from a Let are the leaves from the expression in the body.
leaves (CaseExp l listPE) leavesList = let ei = map extractEfromPair listPE --Extract the expressions from the cases.
                                            in leavesHelper ei leavesList -- Leaves from a Case are the union of the leaves from the expression of each case.
leaves (RLet l1 f l2 e) leavesList = leaves e leavesList --Leaves from a rLet are the leaves from the expression in the body.
leaves (LeftExp l) leavesList = l : leavesList -- A left-exp is a leaf.


leavesHelper :: [E] -> [L] -> [L] --Helper function for leaves in a Case expression.
leavesHelper [] _ = []
leavesHelper listE leavesList = leaves (head listE) leavesList ++ leavesHelper (tail listE) leavesList

extractEfromPair :: (L,E) -> E
extractEfromPair le = snd le

