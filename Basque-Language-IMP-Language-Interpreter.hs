-- Basque IMP Language Interpreter
-- Caleb Long and Devin Crumbley

-- The purpose of this project will be to develop a Haskell program that will act as an 
-- interpreter for a custom programming language of our creation consisting entirely of 
-- words from the Basque dictionary and perform its calculations. This language is 
-- based in implementation upon the IMP language taught in class, chosen due to its 
-- expandability and our familiarity and fondness with it. It would be capable of 
-- performing simple arithmetic calculations as well as defining functions for use later in 
-- the language. We would also like to implement if/then/else statements, 
-- increment/decrement operators, for loops, and switch statements in our language. 
-- Variables are the only thing written in Latin alphanumeric characters to help 
-- differentiate them. Our language would be entirely integer-based, with functions 
-- taking pre-assigned variables as input and editing certain environment variables which
-- can then be read. Our goal would be for it to be a perfectly functional and Turing-complete
-- language capable of use by anyone familiar with the Basque language, 
-- specifically for young minds who speak it.

import Data.Char

-- Main function -- takes user input and returns the system environments.
-- Commented out statements show progress through the interpreter.
main :: IO ()
main = do
    putStrLn "Enter a file to load: "
    filename <- getLine
    input <- readFile filename
    let lexed = lexer input
    -- putStrLn("Lexed: " ++ show lexed)
    let parsed = sr [] lexed
    -- putStrLn("Parsed: " ++ show parsed)
    let result = exec (Do (reverse (parseInstruction (parsed)))) []
    putStrLn (show result) 

-- Expressions to be used between
data NumExpr = Var Vars | Const Integer | Add NumExpr NumExpr | Sub NumExpr NumExpr
           | Mul NumExpr NumExpr | Div NumExpr NumExpr | Exp NumExpr NumExpr | Mod NumExpr NumExpr
           | NEInstr Instr -- Used to wrap instructions in a NumExpr for certain applications
  deriving Show

-- Expressions used between BoolExpressions
data BoolExpr = TT | FF | And BoolExpr BoolExpr | Or BoolExpr BoolExpr | Not BoolExpr
           | Eq  NumExpr NumExpr | Lt  NumExpr NumExpr | Lte NumExpr NumExpr
  deriving Show


-- The main data type in the program, used to hold each specific instruction
data Instr = Assign Vars NumExpr | IfThenElse BoolExpr Instr Instr | While BoolExpr Instr
           | Do [Instr] | Nop | For NumExpr BoolExpr Instr Instr | Switch IntInstPairs NumExpr
           | Function Vars | Inc Vars | Dec Vars | Num Integer -- used to hold a number in the system environment
  deriving Show

-- Custom types
type Env = [(Vars,Instr)] -- Used to hold the current system environment; takes either instructions in the case
                          -- of a function or an instruction-wrapped integer in the case of a variable.
type IntInstPairs = [(Integer,Instr)] -- Used as a switch table
type Vars = String -- Used to represent a custom named variable

-- Operators between NumExprs and BoolExprs
data UOps = NotOp deriving Show
data BOps = AddOp | SubOp | MulOp | DivOp | ModOp | ExpOp
          | AndOp | OrOp  | EqOp  | LtOp  | LteOp | DecOp | IncOp
  deriving Show

-- Keywords used in the code
data Keywords = IfK | ThenK | ElseK | WhileK | NopK | FunctionK | SwitchK | ForK | DecK | IncK
  deriving Show

-- Used during lexing and parsing to prepare creation of instructions
data Token = VSym String | CSym Integer | BSym Bool
           | UOp UOps | BOp BOps | AssignOp
           | LPar | RPar | LBra | RBra | Semi | Colon | Comma
           | Keyword Keywords
           | Err String
           | PN NumExpr | PB BoolExpr | PI Instr | Block [Instr]
           | IIP IntInstPairs
  deriving Show

-- The reduction function, made to reduce the token string over and over
-- into a list of token-encoded instructions.
sr :: [Token] -> [Token] -> [Token]
-- Variables
sr (VSym x : ts) q = sr (PN (Var x) : ts) q
sr (CSym x : ts) q = sr (PN (Const x) : ts) q
sr (BSym True : ts) q = sr (PB TT : ts) q
sr (BSym False : ts) q = sr (PB FF : ts) q

-- Operations
sr (PN p2 : BOp AddOp : PN p1 : ts) q = sr (PN (Add p1 p2) : ts) q
sr (PN p2 : BOp SubOp : PN p1 : ts) q = sr (PN (Sub p1 p2) : ts) q
sr (PN p2 : BOp MulOp : PN p1 : ts) q = sr (PN (Mul p1 p2) : ts) q
sr (PN p2 : BOp DivOp : PN p1 : ts) q = sr (PN (Div p1 p2) : ts) q
sr (PN p2 : BOp ModOp : PN p1 : ts) q = sr (PN (Mod p1 p2) : ts) q
sr (PN p2 : BOp ExpOp : PN p1 : ts) q = sr (PN (Exp p1 p2) : ts) q
sr (PB p : UOp NotOp : ts) q = sr (PB (Not p) : ts) q
sr (PB p2 : BOp AndOp : PB p1 : ts) q = sr (PB (And p1 p2) : ts) q
sr (PB p2 : BOp OrOp : PB p1 : ts) q = sr (PB (Or p1 p2) : ts) q
sr (PN p2 : BOp EqOp : PN p1 : ts) q = sr (PB (Eq p1 p2) : ts) q
sr (PN p2 : BOp LtOp : PN p1 : ts) q = sr (PB (Lt p1 p2) : ts) q
sr (PN p2 : BOp LteOp : PN p1 : ts) q = sr (PB (Lte p1 p2) : ts) q

-- Assignments (DA)
sr (PN p : AssignOp : PN (Var x) : ts) q = sr (PI (Assign x p) : ts) q

-- Assignments for functions
sr (PI (Do b) : AssignOp : PN (Var x) : ts) q = sr (PI (Assign x (NEInstr (Do b))) : ts) q
sr (Semi : Block i : AssignOp : PN (Var x) : ts) q = sr (PI (Assign x (NEInstr (Do i))) : ts) q

-- Reductions for switch statment crafting
sr (PI i : Colon : PN (Const x) : Comma : PN (Var n) : LPar : Keyword SwitchK : ts) q = sr (IIP [(x, i)] : Comma : PN (Var n) : LPar : Keyword SwitchK : ts) q
sr (PI i : Colon : PN (Const x) : IIP p : Comma : PN (Var n) : LPar : Keyword SwitchK : ts) q = sr ( IIP (p ++ [(x, i)]) : Comma : PN (Var n) : LPar : Keyword SwitchK : ts) q

-- Reductions for While and Nop statements
sr (PI i0 : PB b : Keyword WhileK : ts) q = sr (PI (While b i0) : ts) q
sr (RPar : PI i0 : LPar : PB b : Keyword WhileK : ts) q = sr (PI (While b i0) : ts) q
sr (RPar : PI i0 : LPar : RPar : PB b : Keyword WhileK : ts) q = sr (PI (While b i0) : ts) q
sr (Keyword NopK : ts) q = sr (PI Nop : ts) q

-- Reductions for if/then/else statements
sr (RPar : PI i2 : LPar : Keyword ElseK : RPar : PI i1 : LPar : Keyword ThenK : PB b : Keyword IfK : ts) q = sr (PI (IfThenElse b i1 i2) : ts) q
sr (PN (Var x) : Keyword FunctionK : ts) q = sr (PI (Function (x)) : ts) q

-- Reduction for switch statement finalization
sr (RPar : IIP i : Comma : PN (Var x) : LPar : Keyword SwitchK : ts) q = sr (PI (Switch (i) (Var x)) : ts) q

-- Reduction for for loops
sr (PI (Do b) : RPar : BOp IncOp : Comma : PB i : Comma : PN (Var x): LPar : Keyword ForK : ts) q = sr (PI (For (Var x) (i) ((Inc x)) ((Do b))) : ts) q
sr (PI (Do b) : RPar : BOp DecOp : Comma : PB i : Comma : PN (Var x) : LPar : Keyword ForK : ts) q = sr (PI (For (Var x) (i) ((Dec x)) ((Do b))) : ts) q

-- Reductions for Inc/Dec ops
sr (Semi : PN (Var x) : BOp IncOp : ts) q = sr (PI (Inc x) : ts) q
sr (Semi : PN (Var x) : BOp DecOp : ts) q = sr (PI (Dec x) : ts) q

-- Reductions for blocks and syntax
sr (Semi : Block i : ts) q = sr (Block i : ts) q
sr (RPar : PN p : LPar : ts) q = sr (PN p : ts) q
sr (RPar : PB p : LPar : ts) q = sr (PB p : ts) q
sr (RBra : PI p : LBra : ts) q = sr (PI p : ts) q
sr (RBra : PI i : ts) q = sr (Block [i] : ts) q
sr (RBra : Semi : PI i : ts) q = sr (Block [i] : ts) q
sr (RBra : ts) q = sr (Block [] : ts) q
sr (Block is : PI i : ts) q = sr (Block (i:is) : ts) q
sr (Block is : Semi : PI i : ts) q = sr (Block (i:is) : ts) q
sr (Block is : LBra : ts) q = sr (PI (Do is) : ts) q
sr (Semi : PI y : ts) q = sr (PI y : ts) q
sr (Semi : PN x : ts) q = sr (PN x : ts) q
sr s (i:q) = sr (i:s) q
sr s [] = s

-- The lexer function, used to convert the input string into a list of tokens.
lexer :: String -> [Token]
lexer "" = []
-- First set of word matches
lexer s | take 4 s == "EZOP" = Keyword NopK : lexer (drop 4 s)
lexer s | take 2 s == "EZ" = UOp NotOp : lexer (drop 2 s)
lexer s | take 3 s == "ETA" = BOp AndOp : lexer (drop 3 s)
lexer s | take 3 s == "EDO" = BOp OrOp : lexer (drop 3 s)
lexer s | take 8 s == "BERDINAK" = BOp EqOp : lexer (drop 8 s)
lexer s | take 14 s == "BERDINGUTXIAGO" = BOp LteOp : lexer (drop 14 s)
lexer s | take 8 s == "GUTXIAGO" = BOp LtOp : lexer (drop 8 s)
lexer s | take 6 s == "GEHITU" = BOp AddOp : lexer (drop 6 s)
lexer s | take 8 s == "BIDEKATU" = BOp MulOp : lexer (drop 8 s)
lexer s | take 5 s == "KENDU" = BOp SubOp : lexer (drop 5 s)
lexer s | take 6 s == "ZATITU" = BOp DivOp : lexer (drop 6 s)
lexer s | take 7 s == "MODULUA" = BOp ModOp : lexer (drop 7 s)
lexer s | take 8 s == "ERAKUSLE" = BOp ExpOp : lexer (drop 8 s)

-- Simple non-word matches
lexer ('(':s) = LPar : lexer s
lexer (')':s) = RPar : lexer s
lexer ('{':s) = LBra : lexer s
lexer ('}':s) = RBra : lexer s
lexer (';':s) = Semi : lexer s
lexer (':':s) = Colon : lexer s
lexer (',':s) = Comma : lexer s

-- Second set of word matches
lexer s | take 2 s == "DA" = AssignOp : lexer (drop 2 s)
lexer s | take 10 s == "GEHIKUNTZA" = BOp IncOp : lexer (drop 10 s)
lexer s | take 7 s == "GUTXITU" = BOp DecOp : lexer (drop 7 s)
lexer s | take 4 s == "BADA" = Keyword IfK : lexer (drop 4 s)
lexer s | take 4 s == "GERO" = Keyword ThenK : lexer (drop 4 s)
lexer s | take 7 s == "BESTELA" = Keyword ElseK : lexer (drop 7 s)
lexer s | take 9 s == "BITARTEAN" = Keyword WhileK : lexer (drop 9 s)
lexer s | take 10 s == "ETENGAILUA" = Keyword SwitchK : lexer (drop 10 s)
lexer s | take 7 s == "RENTZAT" = Keyword ForK : lexer (drop 7 s)
lexer s | take 8 s == "FUNTZIOA" = Keyword FunctionK : lexer (drop 8 s)
lexer s | take 4 s == "EGIA" = BSym True : lexer (drop 4 s)
lexer s | take 7 s == "FALTSUA" = BSym False : lexer (drop 7 s)

-- Matches negative numbers
lexer ('-':c:s) | isDigit c = let (ds,rs) = span isDigit s in CSym (negate (read (c:ds))) : lexer rs

-- Matches positive numbers
lexer (c:s) | isDigit c = let (ds,rs) = span isDigit s in CSym (read (c:ds)) : lexer rs

-- Matches variables
lexer (c:s) | isLower c = let (vs,rs) = span isAlphaNum s in VSym (c:vs) : lexer rs
lexer (c:s) | isSpace c = lexer s
lexer s = error ("Unrecognized token: " ++ s)

-- Evaluates NumExprs
evalNum :: Env -> NumExpr -> Integer
evalNum env (Var x) = case lookUp env x of
    (Num y) -> y
    _ -> error $ "error in evalnum with numexpr " ++ show x
evalNum env (Const v) = v
evalNum env (Add p1 p2) = evalNum env p1 + evalNum env p2
evalNum env (Sub p1 p2) = evalNum env p1 - evalNum env p2
evalNum env (Mul p1 p2) = evalNum env p1 * evalNum env p2
evalNum env (Div p1 p2) = evalNum env p1 `div` evalNum env p2
evalNum env (Exp p1 p2) = evalNum env p1 ^ evalNum env p2
evalNum env (Mod p1 p2) = evalNum env p1 `mod` evalNum env p2

-- Evaluates BoolExprs
evalBool :: Env -> BoolExpr -> Bool
evalBool _ TT = True
evalBool _ FF = False
evalBool e (And b1 b2) = evalBool e b1 && evalBool e b2
evalBool e (Or b1 b2) = evalBool e b1 || evalBool e b2
evalBool e (Not b) = not $ evalBool e b
evalBool e (Eq e1 e2) = evalNum e e1 == evalNum e e2
evalBool e (Lt e1 e2) = evalNum e e1 < evalNum e e2
evalBool e (Lte e1 e2) = evalNum e e1 <= evalNum e e2

-- Executes the complex instructions
exec :: Instr -> Env -> Env
-- Assigning of functions
exec (Assign x (NEInstr v)) e = update (x, v) e
-- Assigning of variables
exec (Assign x v) e = update (x, Num (evalNum e v)) e

-- Statements
exec (IfThenElse c i1 i2) e = if evalBool e c then exec i1 e else exec i2 e
exec (While c i) e = if evalBool e c then exec (While c i) (exec i e) else e
exec (Switch x (Var i)) e = exec (findInst x (lookUp e i)) e
exec (For (Var z) c (Inc x) b) e = if evalBool e c then exec (For (Var z) c (Inc x) b) (exec (Inc z) (exec b e)) else e
exec (For (Var z) c (Dec x) b) e = if evalBool e c then exec (For (Var z) c (Dec x) b) (exec (Dec z) (exec b e)) else e
exec (Function x) e = exec (lookUp e x) e
exec (Inc x) e = update (x, Num (unNum (lookUp e x) + 1)) e
exec (Dec x) e = update (x, Num (unNum (lookUp e x) - 1)) e
exec (Do []) e = e
exec (Do (i:is)) e = exec (Do is) (exec i e)
exec Nop e = e
exec (Num i) e = e
exec x y = error $ "Stuck in exec: " ++ show x ++ ", " ++ show y

-- Finds a variable or function given a Var
lookUp :: Env -> Vars -> Instr
lookUp [] y = error $ "Variable not found: " ++ y
lookUp ((x,z):xs) y = if (x == y) then z else lookUp xs y

-- Adds or updates a variable or function given a var
update :: (Vars, Instr) -> Env -> Env
update (x,newval) [] = [(x,newval)]
update (x,newval) ((y,v) : e) | x == y = (x,newval) : e
                            | otherwise = (y,v) : update (x,newval) e

-- Parses a list of token-wrapped instructions into a token list
parseInstruction :: [Token] -> [Instr]
parseInstruction [] = []
parseInstruction [PI x] = [x]
parseInstruction ((PI x) : xs) = parseInstruction [PI x] ++ parseInstruction xs
parseInstruction x = error $ "Stuck in parseInstruction: " ++ show x

-- Used by the Switch statement to determine which branch to take
findInst :: IntInstPairs -> Instr -> Instr
findInst ((x,y):xs) (Num z) = if (x == z) then (y) else findInst xs (Num z)
findInst x y = error $ "Stuck in findInst: " ++ show x ++ ", " ++ show y

-- Unwraps an Instr-wrapped integer so that math can be applied to it
unNum :: Instr -> Integer
unNum (Num x) = x
unNum e = error $ "Bad input passed to unNum: " ++ show e
