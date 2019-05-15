{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-tabs #-}

import Data.List
import Data.Char
import Text.Parsec
import Text.Parsec.String
import qualified Text.PrettyPrint as PP

data Term = Var String
		  | Application Term Term
		  | Abstraction String Term
		  deriving(Show,Eq)

data Result = Res Term Int [Term] [String] deriving(Show,Eq)

-------------------- PARSER --------------------------------

lambdaTerm :: Parser Term
lambdaTerm = lambdaAbstraction <|> lambdaApplication <|> simple

lambdaAbstraction :: Parser Term
lambdaAbstraction = do
  	char '\\'
  	var <- letter
  	char '.'
  	body <- lambdaTerm
  	return(Abstraction [var] body)

lambdaApplication :: Parser Term
lambdaApplication = do
  apps <- many1 simple
  return(foldl1 Application apps)

simple :: Parser Term
simple = lambdaVar <|> paren

lambdaVar :: Parser Term
lambdaVar = do
  var <- letter
  return(Var [var])

paren :: Parser Term
paren = do
  char '('
  term <- lambdaTerm
  char ')'
  return term

myparse :: String -> Term
myparse str = case (parse lambdaTerm "" str) of
	Left msg -> error $ show msg
	Right term' -> term'

test = myparse "\\z.(\\f.\\x.fzx)(\\y.y)"
pair = myparse "\\x.\\y.\\z.zxy"

----------------------- PRETTY PRINT ------------------------

ppr :: Term -> PP.Doc
ppr (Var x) = PP.text x
ppr (Abstraction x e) = PP.fcat [(PP.fcat [PP.text "\\",PP.text x,PP.text "."]),(ppr e)]
ppr apply = PP.fcat (map parenApp (args apply))


args (Application x y) = args x ++ [y]
args x = [x]

parenApp (x@(Application _ _)) = PP.parens (ppr x)
parenApp (x@(Abstraction _ _)) = PP.parens (ppr x)
parenApp x = ppr x

prettyprint :: Term -> String
prettyprint term = PP.render (ppr term)

myunwords :: [String] -> String
myunwords [] = []
myunwords (x:xs) = x ++ myunwords xs
 
trim :: String -> String
trim = myunwords . words

------------------------ TEST CASES ------------------------

inputString = "(\\x.\\y.x)(\\z.z)"

parseInputString = myparse inputString

myterm = Application (Abstraction "x" ( Abstraction "y"  (Var "x"))) (Abstraction "z" ( Var "z"))

prettyPrinted = prettyprint myterm


---------------------- main function ----------------------

reduce :: Term -> Result
reduce term = red term 0 [] [] 

red :: Term -> Int -> [Term] -> [String]-> Result
red term counter list1 list2 | ((beta term) == (myparse "false")) = Res (myparse "false") (-1) [] []
                             | ((term == (beta term)) && (term == (eta term))) = Res term counter list1 list2
                             | ((term == (beta term)) == False) = red (beta term) (counter+1) (list1++[beta term]) (list2++["beta"])
			                 | ((term == (beta term)) && ((term == (eta term)) == False)) = red (eta term) (counter+1) (list1++[(eta term)]) (list2++["eta"])


------------------- beta reduction --------------------------

beta :: Term -> Term
beta term = case term of
    Application (Abstraction s t1) t2 -> if ((replace t1 s t2) == term) then myparse "false"
                                         else replace t1 s t2
    Application (Application t1 t2) t3 -> Application (beta (Application t1 t2)) t3
    Application (Var x) t1-> Application (Var x) (beta t1)
    Abstraction x term1 -> (Abstraction x (beta term1))
    _ -> term


-------------------- eta reduction --------------------------

eta :: Term -> Term
eta term = case term of
    Application term1 term2 -> (Application (eta term1) (eta term2))
    Abstraction x (Var y) -> term
    Abstraction x (Application term1 (Var y)) -> if ((x==y) && (member x (fv term1 []) == False)) then term1 
	                                             else term
    Abstraction x (Abstraction y term1) -> Abstraction x (eta (Abstraction y term1))
    _ -> term


---------------------- free variables ---------------------

fv :: Term -> [String] -> [String]
fv term list = case term of  
	Var s -> [s]
	Application term1 term2 ->  returnfv ((fv term1 list) ++ (fv term2 list)) list
	Abstraction bounded y -> returnfv (fv y (list++[bounded])) (list++[bounded])

f :: Term -> String
f x = case x of  
	Var s -> s
	Application x1 y -> f x1
	Abstraction x1 y -> f y

returnfv :: [String] -> [String] -> [String]
returnfv xs [] = oneEachElem xs
returnfv xs (l:list) = returnfv (mydelete l xs) list


-------------------- replacements -------------------------

replace :: Term -> String -> Term -> Term
replace term1 x term2 = case term1 of
    Var s ->  if x == s then term2
	          else term1
    Application t1 t2 -> (Application (replace t1 x term2) (replace t2 x term2))	
    Abstraction s term ->  if (x == s) then term1
                           else (if ((member s (fv term2 []) == False)  ||  (member x (fv term []) == False)) 
                                 then (Abstraction s (replace term x term2))
                                else  replace (Abstraction newS newTerm) x term2)
								where (newS, newTerm) = (findDiffBounded s 97 term term2, replace term s (Var newS))


findDiffBounded :: String -> Int -> Term -> Term -> String			
findDiffBounded s g term term2 = if ((s == [chr g]) || ((member ([chr g]) (fv term [])) == True) || ((member ([chr g]) (fv term2 [])) == True))
                                 then findDiffBounded s (g+1) term term2
								 else [chr g]


--------------------- Logic Values ---------------------

true = "(\\x.\\y.x)" 
false = "(\\x.\\y.y)"
notnot = "(\\z.z(\\x.\\y.y)(\\x.\\y.x))"
condition = "(\\z.\\x.\\y.zxy)"

logicnot :: String -> String
logicnot x = if (x == true) then (prettyprint (returnTerm (reduce (myparse (notnot ++ true)))))
        else (prettyprint (returnTerm (reduce (myparse (notnot ++ false)))))

cond :: String -> String -> String -> String
cond b n m = (prettyprint (returnTerm (reduce (myparse (condition ++ b ++ n ++ m)))))


returnTerm :: Result -> Term
returnTerm (Res term counter list1 list2) = term 


--------------------- Arranged Pairs ----------------------

first :: String -> String -> String
first n m = (prettyprint (returnTerm (reduce (myparse ("(\\z.z(\\x.\\y.x))" ++ (pairs n m))))))

second :: String -> String -> String
second n m = (prettyprint (returnTerm (reduce (myparse ("(\\z.z(\\x.\\y.y))" ++ (pairs n m))))))

pairs :: String -> String -> String
pairs n m = "((\\x.\\y.\\z.zxy)" ++ n ++ m ++ ")"


--------------------- Church Numerals ---------------------

data Cc = C Int deriving(Show,Eq)

findNum :: Int -> Term
findNum n = if (n>0) then (Application (Var "f") (findNum (n-1)))
         else (Application (Var "") (Var "x"))

c :: Cc -> String
c (C n) = prettyprint (Abstraction "f" (Abstraction "x" (findNum n)))

successor :: Cc -> String
successor (C n) = c (C (n+1))


add :: Cc -> Cc -> String
add (C n) (C m) = c (C (n+m))

mult :: Cc -> Cc -> String
mult (C n) (C m) = c (C (n*m))

expon :: Cc -> Cc -> String
expon (C n) (C m) = if (m>0) then (c (C (n^m)))
                    else "False m"


--------------------- USEFULL FUNCTIONS ---------------------

mydelete x [] = []
mydelete x (y:xs) = if (x==y) then mydelete x xs
else y:mydelete x xs

oneEachElem [] = []
oneEachElem [l] = [l]
oneEachElem (l:ls) = if (member l ls == True) then oneEachElem ls 
                     else l:oneEachElem ls

member x [] = False
member x (y:ys) = if (x==y) then True
                 else (member x ys)