I wrote this code in 2012 for a competition for an internship, which I declined
in favor of a different opportunity. It is intended to analyze a program in an
excel-like language, and perform common subexpression elimination on the
program. I haven't touched it since 2012, so it is unlikely to compile, given
the manual Typeable instances. I present it as an artifact, however.

------------------------------------------------------------------------------

This file is a literate Haskell file, meaning that everything outside of the
begin{code}/end{code} blocks is a comment.  GHC is the Glasgow Haskell Compiler,
which is freely available at http://www.haskell.org/platform/

To run the code on formulas stored in filename.txt, see the following sets of
commands.

$ # install the lens and parsec libraries; needed before compilation
$ cabal install lens parsec
$ ghc -O2 -o tokenizer Tokenizer.lhs
$ # generate tables from a series of assignments in filename.txt
$ ./tokenizer --table filename.csv output.csv
$ # perform common subexpression elimination on the program defined in filename.txt
$ ./tokenizer --optimize filename.csv output.csv

We start with the necessary imports and language extensions:

\begin{code}
{-# LANGUAGE StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances, NoMonomorphismRestriction, OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables, DeriveDataTypeable #-}

module Main where

import Prelude hiding (lookup)

import Control.Applicative ((<$>), (<*>), (*>), (<*))
import Control.Lens
import qualified Control.Monad.State as State

import Data.Char
import Data.Data hiding (Infix)
import Data.Data.Lens
import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.Traversable
import Data.Typeable

import System.Environment
import System.Exit
import System.Console.GetOpt

import Text.Parsec.Expr
import Text.ParserCombinators.Parsec hiding (try, runParser) -- parser combinators
import Text.Parsec.Prim
import Text.Parsec.Text
\end{code}

First, we need a datatype to represent an annotated version of our syntax tree.
This infinite datatype, which goes by the name of "functor fixpoint", is
described at length elsewhere, but the intuition is that Fix and Ann allow
arbitrarily deep nesting of a plain container annotated with source information.
The following instances are uninteresting; they are necessary to allow generic
programming with Control.Lens.Plated.

\begin{code}
newtype Fix f = In { out :: f (Fix f) }

deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)
deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance (Typeable1 f, Data (f (Fix f))) => Data (Fix f)

data Ann x f a = Ann x (f a) deriving (Show, Functor, Traversable, Foldable.Foldable)

instance (Eq (f a)) => Eq (Ann x f a) where
    (Ann _ x) == (Ann _ y) = x == y

instance (Ord (f a)) => Ord (Ann x f a) where
    compare (Ann _ x) (Ann _ y) = compare x y

deriving instance (Data (f a), Data x, Typeable a, Typeable1 f) => Data (Ann x f a)

instance (Typeable x, Typeable1 f) => Typeable1 (Ann x f) where
    typeOf1 _ = mkTyConApp tc [typeOf (undefined :: x), typeOf1 (undefined :: f a)]
        where tc = mkTyCon3 "Tokenizer" "Main" "Ann"

instance (Typeable1 f) => Typeable (Fix f) where
    typeOf _ = mkTyConApp tc [typeOf1 (undefined :: f a)]
        where tc = mkTyCon3 "Tokenizer" "Main" "Fix"
\end{code}

The top level of our language will be a list of assignments, leading
to the obvious implementation of our toplevel.

\begin{code}
type Toplevel = [(ExprA, ExprA)]
\end{code}

In a full-fledged programming language, correctly representing and manipulating
variables is a devilishly tricky business to get right.  However, this language
is simple enough that we can represent a variable as an integer.  The nth
variable defined is represented as n, but we keep the variable for error
reporting.

\begin{code}
data Var a = Var Int deriving (Show, Ord, Eq, Typeable, Data)
type Msg  = (SourcePos, Text.Text)
type VarA = Fix (Ann Msg Var)

type VarMap = (Int, Map.Map Text.Text Int)
\end{code}

Now the meat of our program is defined: the expression.  This language has
variables, integer and double literals, and a variety of mathematical and
logical function calls.

\begin{code}
data Literal = Double Double
             | Int Int
               deriving (Show, Eq, Ord, Data, Typeable)

data Expr a = EVar VarA
            | ELit Literal
            | Add a a
            | Sub a a
            | Mul a a
            | Div a a
            | Pow a a
            | Lt  a a
            | Gt  a a
            | Eql a a
            | Geq a a
            | Leq a a
            | Fn Text.Text [a]
              deriving (Show, Eq, Ord, Functor, Foldable.Foldable
                       , Traversable, Data, Typeable)

type ExprA = Fix (Ann Msg Expr)

-- allow for generic programming with uniplate
instance Data a => Plated (Expr a) where
   plate = uniplate

instance Plated ExprA where
    plate = uniplate
\end{code}

Now we are ready to begin the actual process of parsing the input data.  We
start with the easiest tokens - variables.  Variables are a sequence of letters
and underscores.

\begin{code}
variable :: Stream s m Char => ParsecT s VarMap m ExprA
variable = do p <- getPosition
              v <- satisfy isAlpha
              vs <- many (satisfy predicate)
              (n,hmap) <- getState
              let msg = (p, Text.pack $ v:vs)
              case Map.lookup (snd msg) hmap of
                Nothing -> do putState (n+1, Map.insert (snd msg) n hmap)
                              ret msg n
                Just m  -> ret msg m

    where predicate ch = isAlpha ch || ch == '_' || isDigit ch
          var m n = In $ Ann m n
          ret msg n = return . var msg . EVar $ var msg (Var n)
\end{code}

Integers are an optional minus sign, followed by a sequence of digits.

\begin{code}
integer :: Stream s m Char => ParsecT s u m ExprA
integer = do pos <- getPosition
             s <- optionMaybe (char '-')
             let f = case s of
                       Nothing -> id
                       Just m  -> (m:)
             digits <- many1 digit
             return $ int f pos digits
    where int f p n = In $ Ann (p, Text.pack n) (ELit . Int . read $ f n)
\end{code}

Doubles are a bit more complicated.  They have an optional minus sign, followed
by an integer and an exponent (i.e. "4e4"), or an integer, decimal point,
fraction, and optional exponent (i.e. "4.0", "-2.4e-1").

\begin{code}
double :: Stream s m Char => ParsecT s u m ExprA
double = do pos <- getPosition
            dec <- int
            end <- try exp <|> frac
            return . doub pos $ dec ++ end
    where exp = do e <- oneOf "eE"
                   i <- int
                   return $ e:i
          frac   = do dot <- char '.'
                      digits <- many1 digit
                      e <- optionMaybe exp
                      return $ (dot:digits) ++ (fromMaybe [] e)
          int = do s <- optionMaybe $ char '-'
                   let f = case s of
                             Nothing -> id
                             Just m  -> (m:)
                   digits <- many1 digit
                   return $ f digits
          doub p n = In $ Ann (p, Text.pack n) (ELit . Double $ read n)
\end{code}

Next, we define a parser for function calls, which are of the form
"function(arg1, arg2, ..., argn)".

\begin{code}
funcall :: Stream s m Char => ParsecT s VarMap m ExprA
funcall = do In (Ann m@(_,v) _) <- variable
             args <- parens $ sepBy1 expr comma
             return . In . Ann m $ Fn v args
    where comma = lexeme $ char ','
\end{code}

Our language would be painful to use without operators, so let's add some.
These functions return a function that is annotated with the location of the
call site.

\begin{code}
optbl = [ [binary "^" Pow AssocLeft]
        , [binary "*" Mul AssocLeft, binary "/" Div AssocLeft ]
        , [binary "+" Add AssocLeft, binary "-" Sub AssocLeft ]
        , [ binary "<" Lt  AssocNone, binary ">" Gt  AssocNone
          , binary "==" Eql AssocNone, binary "<=" Leq AssocNone
          , binary ">=" Geq AssocNone
          ]
        ]
    where binary name fun assoc =
            Infix (do lexeme $ string name
                      p <- getPosition
                      return (\e1 e2 ->
                               In (Ann (p,Text.pack name) (fun e1 e2))))
            assoc
\end{code}

We can now define an expression parser, with the aid of Parsec's helpfully named
buildExpressionParser.

\begin{code}
expr :: Stream s m Char => ParsecT s VarMap m ExprA
expr = buildExpressionParser optbl base

base :: Stream s m Char => ParsecT s VarMap m ExprA
base   = try (lexeme double)
         <|> lexeme integer
         <|> try (lexeme funcall)
         <|> (lexeme variable)
         <|> (parens expr)
\end{code}

Now we can parse an assignment, which is terminated with a semi-colon, and from
there, a whole program.

\begin{code}
assignment :: Stream s m Char => ParsecT s VarMap m (ExprA, ExprA)
assignment = do v <- lexeme variable
                _ <- lexeme $ char '='
                e <- expr
                _ <- lexeme $ char ';'
                return (v,e)

toplevel :: Stream s m Char => ParsecT s VarMap m Toplevel
toplevel = many1 assignment
\end{code}

Lexeme takes a parser as an argument, and returns a new parser that consumes all
the whitespace after its argument succeeds.  Parens also takes a parser p as an
argument, and returns a new parser that recognizes p between parens.

\begin{code}
parens, lexeme :: Stream s m Char => ParsecT s u m a -> ParsecT s u m a
parens p = (lexeme $ char '(') *> lexeme p <* (lexeme $ char ')')
lexeme p = p <* many (satisfy isSpace)
\end{code}

We are now ready to begin common subexpression elimination.  The free variable
in the Expr datatype will come in handy - we can instantiate it with an integer,
which will hold a hash of the expression.  We'll call this new datatype
ExprNode, and will transform the program into a directed acyclic graph of these
nodes.  Since ExprNode is a non-recursive datatype, checking two nodes for
equality takes constant time.

To implement the directed acyclic graph, we'll use a bidirectional map.

\begin{code}
type ExprNode = Expr Int
newtype DAG = DAG (BiMap ExprNode) deriving Show
newtype Node = Node { unNode :: State.State DAG Int }

data BiMap a = BiMap (Map.Map a Int) (IntMap.IntMap a)

lookupKey :: Ord k => k -> BiMap k -> Maybe Int
lookupKey v (BiMap m _) = Map.lookup v m

lookupVal :: IntMap.Key -> BiMap a -> Maybe a
lookupVal k (BiMap _ m) = IntMap.lookup k m

insert :: Ord a => a -> BiMap a -> (Int, BiMap a)
insert v (BiMap m im) = (k, BiMap m' im')
    where k = IntMap.size im
          im' = IntMap.insert k v im
          m' = Map.insert v k m

empty :: BiMap a
empty = BiMap Map.empty IntMap.empty

instance Show a => Show (BiMap a) where
    show (BiMap _ m) = "BiMap" ++ show (IntMap.toList m)

size :: BiMap a -> Int
size (BiMap _ im) = IntMap.size im
\end{code}

Now it's time to use the BiMap.  Given a node, either insert it or return the
existing value.

\begin{code}
hashcons :: ExprNode -> State.State DAG Int
hashcons e = do DAG m <- State.get
                case lookupKey e m of
                  Nothing -> let (k, m') = insert e m
                             in State.put (DAG m') >> return k
                  Just k  -> return k
\end{code}

'elimCommonSubExprs' eliminates common subexpressions in an expression.  Be
careful when using it, though, since operators are left-associative; the
expression "a+a+a+a" is parsed as "a+(a+(a+a))", which has no common
subexpressions to eliminate.  However, the expression "(a+a)+(a+a)" does have a
common subexpression, "a+a".  A more complete optimizer would include an
expression balancer and a redundant assignment eliminator, but in the interest
of brevity, I have elected to not implement these here.

\begin{code}
elimCommonSubExprs :: ExprA -> State.State DAG (ExprNode, Int)
elimCommonSubExprs e = case e of
           (In (Ann _ (EVar v))) -> do let v' = EVar v
                                       h <- hashcons v'
                                       return (v', h)
           (In (Ann _ (ELit l))) -> do let l' = ELit l
                                       h <- hashcons l'
                                       return (l', h)
           (In (Ann _ (Add e1 e2))) -> binop Add e1 e2
           (In (Ann _ (Sub e1 e2))) -> binop Sub e1 e2
           (In (Ann _ (Mul e1 e2))) -> binop Mul e1 e2
           (In (Ann _ (Div e1 e2))) -> binop Div e1 e2
           (In (Ann _ (Pow e1 e2))) -> binop Pow e1 e2
           (In (Ann _ (Lt  e1 e2))) -> binop Lt  e1 e2
           (In (Ann _ (Gt  e1 e2))) -> binop Gt  e1 e2
           (In (Ann _ (Eql e1 e2))) -> binop Eql e1 e2
           (In (Ann _ (Geq e1 e2))) -> binop Geq e1 e2
           (In (Ann _ (Leq e1 e2))) -> binop Leq e1 e2
           (In (Ann _ (Fn name args))) -> do args' <- State.mapM elimCommonSubExprs args
                                             let e = Fn name (map snd args')
                                             h <- hashcons e
                                             return (e,h)
    where binop con e1 e2 = do h1 <- elimCommonSubExprs e1
                               h2 <- elimCommonSubExprs e2
                               let e = con (snd h1) (snd h2)
                               h <- hashcons e
                               return (e,h)

cseProgram :: [(ExprA, ExprA)] -> DAG
cseProgram top = foldl cseExpr (DAG empty) (map snd top)
    where cseExpr dag expr = snd $ State.runState (elimCommonSubExprs expr) dag
\end{code}

Next, we'll implement the code necessary to generate and output the tables and
optimized code.

\begin{code}
showExpr :: ExprA -> Text.Text
showExpr e = showExpr' e True
    where showExpr' e top = case e of
               (In (Ann (_,v) (EVar _))) -> v
               (In (Ann _ (ELit l))) -> case l of
                                          Double d -> Text.pack $ show d
                                          Int    i -> Text.pack $ show i
               (In (Ann _ (Add e1 e2))) -> Text.concat $ showBinop "+" e1 e2
               (In (Ann _ (Sub e1 e2))) -> Text.concat $ showBinop "-" e1 e2
               (In (Ann _ (Mul e1 e2))) -> Text.concat $ showBinop "*" e1 e2
               (In (Ann _ (Div e1 e2))) -> Text.concat $ showBinop "/" e1 e2
               (In (Ann _ (Pow e1 e2))) -> Text.concat $ showBinop "^" e1 e2
               (In (Ann _ (Gt  e1 e2))) -> Text.concat $ showBinop ">" e1 e2
               (In (Ann _ (Lt  e1 e2))) -> Text.concat $ showBinop "<" e1 e2
               (In (Ann _ (Eql e1 e2))) -> Text.concat $ showBinop "==" e1 e2
               (In (Ann _ (Geq e1 e2))) -> Text.concat $ showBinop ">=" e1 e2
               (In (Ann _ (Leq e1 e2))) -> Text.concat $ showBinop "<=" e1 e2
               (In (Ann _ (Fn name args))) -> Text.concat [name
                                                          , "("
                                                          , Text.intercalate "," $
                                                               map showExpr args
                                                          , ")"]
              where showBinop op e1 e2 = [if top then "" else "("
                                         , showExpr' e1 False
                                         , op
                                         , showExpr' e2 False
                                         , if top then "" else ")" ]

table :: ExprA -> [[Text.Text]]
table expr = concat $ table' expr
    where table' expr = rows expr:(concat . map table' $ children expr)
          rows e = let c = length (children e)
                   in map row $ zip (replicate c e) [1..]
          row (e,i) = let c = children e !! (i-1)
                      in [showExpr e
                      , opstr e
                      , Text.pack . show $ i
                      , showExpr c
                      , Text.pack . show $ isVariable c
                      , Text.pack . show $ isNumber c]
          isNumber (In (Ann _ (ELit _))) = True
          isNumber _ = False
          isVariable (In (Ann _ (EVar _))) = True
          isVariable _ = False
          opstr e = case e of
                      (In (Ann _ (Add _ _))) -> "+"
                      (In (Ann _ (Sub _ _))) -> "-"
                      (In (Ann _ (Mul _ _))) -> "*"
                      (In (Ann _ (Div _ _))) -> "/"
                      (In (Ann _ (Pow _ _))) -> "^"
                      (In (Ann _ (Gt  _ _))) -> ">"
                      (In (Ann _ (Lt  _ _))) -> "<"
                      (In (Ann _ (Eql _ _))) -> "=="
                      (In (Ann _ (Geq _ _))) -> ">="
                      (In (Ann _ (Leq _ _))) -> "<="
                      (In (Ann _ (Fn f _)))  -> f

varName = "var"

showOpt' :: (Show a, Show a1) => a -> a1 -> Text.Text -> Text.Text
showOpt' a b o = Text.concat
                 [varName, Text.pack (show a),
                  o, varName, Text.pack (show b)]


showOpt :: (Show a, Show a1) => (a, Expr a1) -> Text.Text
showOpt (i,e) = Text.concat [(Text.pack $ varName ++ show i)
                             , "="
                             , case e of
              (EVar (In (Ann _ (Var v)))) -> Text.append varName (Text.pack $ show v)
              (ELit l) -> case l of
                            Double d -> Text.pack $ show d
                            Int    n -> Text.pack $ show n
              (Add a b) -> showOpt' a b "+"
              (Sub a b) -> showOpt' a b "-"
              (Mul a b) -> showOpt' a b "*"
              (Div a b) -> showOpt' a b "/"
              (Pow a b) -> showOpt' a b "^"
              (Gt  a b) -> showOpt' a b ">"
              (Lt  a b) -> showOpt' a b "<"
              (Eql a b) -> showOpt' a b "=="
              (Geq a b) -> showOpt' a b ">="
              (Leq a b) -> showOpt' a b "<="
              (Fn f args) -> Text.concat [f, "(", Text.intercalate ","
                                                  $ map
                                                  (\a -> Text.pack
                                                         $ varName ++ show a)
                                                  args, ")"]
                            ]

optimized :: Toplevel -> [Text.Text]
optimized top = let DAG (BiMap _ im) = cseProgram top
                    showAssign (v,e) =
                      Text.concat [varName, Text.pack $ show v,
                                   " = ", showOpt e, ";"]
                in map showOpt $ IntMap.toList im
\end{code}

We are now ready to write the driver code that interfaces our logic to the
command line.  The program will either output a table, and/or the code with
common subexpressions eliminated.

\begin{code}
writeTables :: FilePath -> Toplevel -> IO ()
writeTables file top = do TextIO.writeFile file ""
                          mapM_ (TextIO.appendFile file . printTable . formatTable)
                                (filter (\x -> children x /= []) $ map snd top)
    where printTable t =
            Text.concat [ "Calculation; "
                        , "Operation; "
                        , "Token Order; "
                        , "Token; "
                        , "Is Token A Variable; "
                        , "Is Token A Number\n"
                        , t
                        , "\n\n"]
          formatTable t = Text.intercalate "\n"
                        . map (Text.intercalate ";")
                        . filter (\x -> not $ null x)
                        $ table t

writeOptimized :: FilePath -> Toplevel -> IO ()
writeOptimized file top = TextIO.writeFile file
                        . Text.intercalate ";\n"
                        $ optimized top

data Options = Options { opt :: Text.Text
                       , tbl :: Text.Text
                       } deriving Show

options :: [OptDescr (Options -> Options)]
options = [ Option "o" ["optimize"] (ReqArg (\o opts -> opts { opt = Text.pack o })
            "FILENAME") "Output an optimized version of the program in FILENAME."
          , Option "t" ["table"] (ReqArg (\t opts -> opts { tbl = Text.pack t }) "FILENAME")
            "Output a table of the expressions in FILENAME"
          ]

defaultOptions :: Options
defaultOptions = Options { opt = "", tbl = "" }

parseArgs :: IO ([String], Options)
parseArgs = do args <- getArgs
               name <- getProgName
               let help = "Usage: " ++ name ++ " [OPTIONS] INPUT"
               case getOpt RequireOrder options args of
                 (opts, files, []) -> return $ (files,foldl (flip id) defaultOptions opts)
                 (_, _, errs)   -> ioError (userError $ concat errs ++ (usageInfo help options))

main :: IO ()
main = do argv <- parseArgs
          case argv of
            ([], _) -> do putStrLn "Must specify input file."
                          exitWith $ ExitFailure 1
            (file:_, opts) -> do input <- TextIO.readFile file
                                 case runParser toplevel (0, Map.empty) file input of
                                   Left err -> putStrLn $ show err
                                   Right p  -> do if Text.null $ opt opts
                                                  then return ()
                                                  else writeOptimized
                                                           (Text.unpack $ opt opts) p
                                                  if Text.null $ tbl opts
                                                  then return ()
                                                  else writeTables
                                                           (Text.unpack $ tbl opts) p
                                                  exitWith ExitSuccess
\end{code}

Here are the testcases given in the contest description.

v1 = 2*D + A;
v2 = min(B,C,2*D + A);
v3 = C/D^2;
v4 = 2*D + A + min(B,C,2*D + A) - C/D^2;
v5 = Log(4*B + Beta*D);
v6 = if(A > 0, 2*A, A + C);
v7 = Log(4*B + Beta*D) + if(A > 0, 2*A, A + C);

To run the testcases, paste them into a file ("input.csv") and run the following
commands.

$ ghc -O2 -o tokenizer Tokenizer.lhs # if the program is not yet compiled
$ ./tokenizer --table output.csv input.csv

The results should look like this.  Paste them into an Excel spreadsheet for
easier viewing.

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
(2*D)+A;+;1;2*D;False;False
(2*D)+A;+;2;A;True;False
2*D;*;1;2;False;True
2*D;*;2;D;True;False

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
min(B,C,(2*D)+A);min;1;B;True;False
min(B,C,(2*D)+A);min;2;C;True;False
min(B,C,(2*D)+A);min;3;(2*D)+A;False;False
(2*D)+A;+;1;2*D;False;False
(2*D)+A;+;2;A;True;False
2*D;*;1;2;False;True
2*D;*;2;D;True;False

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
C/(D^2);/;1;C;True;False
C/(D^2);/;2;D^2;False;False
D^2;^;1;D;True;False
D^2;^;2;2;False;True

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
(((2*D)+A)+min(B,C,(2*D)+A))-(C/(D^2));-;1;((2*D)+A)+min(B,C,(2*D)+A);False;False
(((2*D)+A)+min(B,C,(2*D)+A))-(C/(D^2));-;2;C/(D^2);False;False
((2*D)+A)+min(B,C,(2*D)+A);+;1;(2*D)+A;False;False
((2*D)+A)+min(B,C,(2*D)+A);+;2;min(B,C,(2*D)+A);False;False
(2*D)+A;+;1;2*D;False;False
(2*D)+A;+;2;A;True;False
2*D;*;1;2;False;True
2*D;*;2;D;True;False
min(B,C,(2*D)+A);min;1;B;True;False
min(B,C,(2*D)+A);min;2;C;True;False
min(B,C,(2*D)+A);min;3;(2*D)+A;False;False
(2*D)+A;+;1;2*D;False;False
(2*D)+A;+;2;A;True;False
2*D;*;1;2;False;True
2*D;*;2;D;True;False
C/(D^2);/;1;C;True;False
C/(D^2);/;2;D^2;False;False
D^2;^;1;D;True;False
D^2;^;2;2;False;True

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
Log((4*B)+(Beta*D));Log;1;(4*B)+(Beta*D);False;False
(4*B)+(Beta*D);+;1;4*B;False;False
(4*B)+(Beta*D);+;2;Beta*D;False;False
4*B;*;1;4;False;True
4*B;*;2;B;True;False
Beta*D;*;1;Beta;True;False
Beta*D;*;2;D;True;False

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
if(A>0,2*A,A+C);if;1;A>0;False;False
if(A>0,2*A,A+C);if;2;2*A;False;False
if(A>0,2*A,A+C);if;3;A+C;False;False
A>0;>;1;A;True;False
A>0;>;2;0;False;True
2*A;*;1;2;False;True
2*A;*;2;A;True;False
A+C;+;1;A;True;False
A+C;+;2;C;True;False

Calculation; Operation; Token Order; Token; Is Token A Variable; Is Token A Number
Log((4*B)+(Beta*D))+if(A>0,2*A,A+C);+;1;Log((4*B)+(Beta*D));False;False
Log((4*B)+(Beta*D))+if(A>0,2*A,A+C);+;2;if(A>0,2*A,A+C);False;False
Log((4*B)+(Beta*D));Log;1;(4*B)+(Beta*D);False;False
(4*B)+(Beta*D);+;1;4*B;False;False
(4*B)+(Beta*D);+;2;Beta*D;False;False
4*B;*;1;4;False;True
4*B;*;2;B;True;False
Beta*D;*;1;Beta;True;False
Beta*D;*;2;D;True;False
if(A>0,2*A,A+C);if;1;A>0;False;False
if(A>0,2*A,A+C);if;2;2*A;False;False
if(A>0,2*A,A+C);if;3;A+C;False;False
A>0;>;1;A;True;False
A>0;>;2;0;False;True
2*A;*;1;2;False;True
2*A;*;2;A;True;False
A+C;+;1;A;True;False
A+C;+;2;C;True;False
