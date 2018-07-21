--Mathias Grønstad
module Oblig1 where
import Data.Char
import Data.Typeable
data Ast = Nr Int | Sum Ast Ast | Mul Ast Ast | Min Ast | If Ast Ast Ast | Let String Ast Ast | Var String deriving (Eq, Show) 

--First we must split the input string into a list of its tokens (taken from exercises in week 4)
tokenize :: String -> [String]
tokenize [] = []
tokenize (' ':xs) = tokenize xs
tokenize ('+':xs) = "+":tokenize xs
tokenize ('*':xs) = "*":tokenize xs
tokenize ('-':xs) = "-":tokenize xs
tokenize ('(':xs) = "(": tokenize xs
tokenize (')':xs) = ")": tokenize xs
--tokenize ('=':xs) = "=": tokenize xs
tokenize('i':'f':xs) = "if" : tokenize xs
tokenize('l':'e':'t':xs) = "let" : tokenize xs
--tokenize('i':'n':xs) = "in" : tokenize xs
tokenize (x:xs) = if isDigit x then (takeWhile isDigit (x:xs)) : tokenize (dropWhile isDigit xs) 
                  else if isUpper x then [x] : tokenize xs
                  else tokenize xs

parse :: String -> Ast
--Function parse sends the tokenized string to the function parseExpre which will create ASTs
--I use'"case" since if parseExpr returns (Ast, []) with an empty list as second arg.
--then the parsing was successful. Otherwise the parsing was unsuccessful, probably due to
--invalid input format.
parse xs = case parseExpr (tokenize xs) of
    (ast, []) -> ast
    otherwise -> error "Couldn't parse. Please check that input is valid."
    
--parseExpr is a recursive function which reads the first token/symbol of the string and pattern matches it 
--Based on its value we return different ASTs while the rest of the string is sent back to parseExpr
--the parse function will return the first argument "Ast" if second argument is an empty list []
--since then string is exhausted and the parsing should be complete
parseExpr :: [String] -> (Ast, [String])
parseExpr ("let":v:rest) = let a = v
                               (b, rest')  = parseExpr rest
                               (c, rest'') = parseExpr rest'
                                in (Let a b c, rest'')
parseExpr ("if":rest) = let (a, rest')  = parseExpr rest
                            (b, rest'') = parseExpr rest'
                            (c, rest''') = parseExpr rest''
                             in (If a b c, rest''')
--if the first token is "+" then the next two tokens should be "a" and "b" in "Sum a b" where a and be are ASTs
parseExpr ("+":rest) = let (a, rest')  = parseExpr rest
                           (b, rest'') = parseExpr rest'
                            in (Sum a b, rest'')
--same as for "+"
parseExpr ("*":rest) = let (a, rest')  = parseExpr rest
                           (b, rest'') = parseExpr rest'
                            in (Mul a b, rest'')
--if the first token is "-" we negate what comes after
parseExpr ("-":rest) = let (a, rest') = parseExpr rest in (Min a, rest')
--if the first token/expression is a number string, we return it as a Nr
parseExpr (a:rest)   = if all isDigit a
                            then (Nr (read a), rest)
--if the first token/expression is a upper case letter (string), we return it as a Var
--reading the string which is a list of a single Char as a Char using !!0
                        else if isUpper (a!!0) 
                            then (Var a, rest)                            
--if no pattern has matched, we have not been able to parse the tokens according to the grammar
                        else error "Could not parse Ast tokens"
--If we cannot match anything above it's an invalid expression
parseExpr _          = error "Error: invalid expression."
   
--First I make a HO function "evaluate" which takes an AST and evaluates it to it's final expression.
--(Similar to folde from Week 5a)
--The function evaluate takes in 4 functions and an AST as arugment. Which funcitons are sent as
--input depends on whether we want to evaluate a boolean or an arithmetic expression.
--To make the function more readable I intorduce new types for the type signature
type Op a = (a -> a -> a)
type Unary a = (a -> a)
evaluate :: Op a -> Op a -> Unary a -> (Int -> a) -> (a -> Bool) -> (Dict String Ast) -> Ast -> a
--I use "case of, where" expressions to avoid repetitive code 
evaluate sum mul min num iff dict exp = case exp of
    (Sum a b)   -> sum (eval dict a) (eval dict b)
    (Mul a b)   -> mul (eval dict a) (eval dict b)
    (Min a)     -> min (eval dict a)
    (Nr  n)     -> num n
    (If a b c)  -> if (iff (eval dict a)) then eval dict b else eval dict c
                        --Initially we set they value of the variable to "Var k", and it the next evaluation it will be bound.
                        --If the variable doesn't get bound, then it is an undecleared variable in the parsed string, and we give an error
                        --If we don't have undecleared variables, we check if the variable is bound by searching dict, and change the value
                        --If the variable is found, then we return its value, since we encounter for second time
    (Var k)     -> if (anyUndecleard dict) then error "Error: undecleared variables in input." 
                   else if (not (findk k dict)) then eval (insert k (Var k) dict) (Var k) else eval dict (findv k dict) 
                        -- a is the key (a,v), b is the new expression so that v = eval dict b. We send the updated dict (d) to eval d b
                        --if the variable "a" is in the dictionary, we update it with the new binding "b"
                        --if not, we encounter for the first time, and we just add the new binding to the dict.                        
    (Let a b c) -> let d = if (findk a dict) then change a b dict else insert a b dict in eval d c
                        --If binding of variables was successful we should not have undecleared variables in dict
                        --We check if there is a "Nr 0" which is what I assigned to variables initailly before they got a binding 
    where
    eval dict = evaluate sum mul min num iff dict

--Dictionary for storing variable value pairs in tuples (From exercises Week 5b)
type Dict n v = [(n, v)]

--Function for finding a Value of a Key in the dict
findv :: Eq n => n -> Dict n v -> v
findv n dict = head [v | (n', v) <- dict, n'==n]

--Function for finding if a Key is in the dict
findk :: Eq n => n -> Dict n v -> Bool
findk n dict = not (null [n | (n', v) <- dict, n'==n])

--Function for inserting a Key/value pair in the dict
insert ::    n => n -> v -> Dict n v -> Dict n v
insert n v dict = (n, v) : dict

--Function for changing the value of a key in the dict 
change :: Eq n => n -> v -> Dict n v -> Dict n v
change n v (x:xs) = (takeWhile(\(n2, v2) -> n2 /= n) (x:xs)) ++ [(n,v)] ++ tail(dropWhile(\(n2, v2) -> n2 /= n) (x:xs))

--Function for finding undecleared variables in the dict 
anyUndecleard :: Dict String Ast -> Bool
anyUndecleard dict =  not (null [n | (n, v) <- dict, Var n == v])

-- Function to evaluate an arithmetic expression
evi :: String -> Int
evi s = evaluate (+) (*) negate id (==0) ([]) (parse s)

-- Function to evaluate a boolean expression
evb :: String -> Bool
evb s = evaluate (||) (&&) not odd (\x -> x == True) ([]) (parse s)