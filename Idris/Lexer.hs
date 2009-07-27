module Idris.Lexer where

import Data.Char
import Debug.Trace

import Idris.AbsSyntax

type LineNumber = Int

type P a = String -> String -> LineNumber -> UserOps -> Result a

getLineNo :: P LineNumber
getLineNo = \s fn l ops -> Success l

getFileName :: P String
getFileName = \s fn l ops -> Success fn

getContent :: P String
getContent = \s fn l ops -> Success s

getOps :: P UserOps
getOps = \s fn l ops -> Success ops

thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \s fn l ops ->
   case m s fn l ops of
       Success a -> k a s fn l ops
       Failure e f ln -> Failure e f ln

returnP :: a -> P a
returnP a = \s fn l ops -> Success a

failP :: String -> P a
failP err = \s fn l ops -> Failure err fn l

catchP :: P a -> (String -> P a) -> P a
catchP m k = \s fn l ops ->
   case m s fn l ops of
      Success a -> Success a
      Failure e f ln -> k e s fn l ops

happyError :: P a
happyError = reportError "Parse error"

reportError :: String -> P a
reportError err = getFileName `thenP` \fn ->
                  getLineNo `thenP` \line ->
		  getContent `thenP` \str ->
                      failP (fn ++ ":" ++ show line ++ ":" ++ err ++ 
                             " - before " ++ take 80 str ++ "...")

data Token
      = TokenName Id
      | TokenInfixName String
      | TokenBrackName Id
      | TokenString String
      | TokenInt Int
      | TokenFloat Double
      | TokenChar Char
      | TokenBool Bool
      | TokenMetavar Id
      | TokenIntType
      | TokenCharType
      | TokenBoolType
      | TokenFloatType
      | TokenStringType
      | TokenHandleType
      | TokenLockType
      | TokenPtrType
      | TokenDataType
      | TokenInfix
      | TokenInfixL
      | TokenInfixR
      | TokenUsing
      | TokenNoElim
      | TokenCollapsible
      | TokenPartial
      | TokenSyntax
      | TokenLazy
      | TokenWhere
      | TokenWith
      | TokenType
      | TokenLazyBracket
      | TokenOB
      | TokenCB
      | TokenOCB
      | TokenCCB
      | TokenOSB
      | TokenCSB
      | TokenConcat
      | TokenPlus
      | TokenMinus
      | TokenTimes
      | TokenDivide
      | TokenEquals
      | TokenOr
      | TokenAnd
      | TokenMightEqual
      | TokenEQ
      | TokenGE
      | TokenLE
      | TokenGT
      | TokenLT
      | TokenArrow
      | TokenFatArrow
      | TokenLeftArrow
      | TokenColon
      | TokenSemi
      | TokenComma
      | TokenTuple
      | TokenBar
      | TokenDot
      | TokenEllipsis
      | TokenLambda
      | TokenInclude
      | TokenDo
      | TokenIf
      | TokenThen
      | TokenElse
      | TokenLet
      | TokenIn
      | TokenRefl
      | TokenEmptyType
      | TokenUnitType
      | TokenUnderscore
      | TokenBang
-- Tactics
      | TokenProof
      | TokenIntro
      | TokenRefine
      | TokenGeneralise
      | TokenReflP
      | TokenRewrite
      | TokenRewriteAll
      | TokenCompute
      | TokenUnfold
      | TokenUndo
      | TokenInduction
      | TokenFill
      | TokenTrivial
      | TokenMkTac
      | TokenBelieve
      | TokenUse
      | TokenDecide
      | TokenAbandon
      | TokenQED
-- Directives
      | TokenLaTeX
      | TokenNoCG
      | TokenEval
      | TokenCInclude
      | TokenCLib
      | TokenEOF
 deriving (Show, Eq)


lexer :: (Token -> P a) -> P a
lexer cont [] = cont TokenEOF []
lexer cont ('\n':cs) = \fn line -> lexer cont cs fn (line+1)
-- empty type
lexer cont ('_':'|':'_':cs) = cont TokenEmptyType cs
lexer cont ('_':c:cs) | not (isAlpha c) && c/='_' = cont TokenUnderscore (c:cs)
lexer cont (c:cs)
      | isSpace c = \fn line -> lexer cont cs fn line
      | isAlpha c = lexVar cont (c:cs)
      | isDigit c = lexNum cont (c:cs)
      | c == '_' = lexVar cont (c:cs)
-- unit type
lexer cont ('(':')':cs) = cont TokenUnitType cs
lexer cont ('"':cs) = lexString cont cs
lexer cont ('\'':cs) = lexChar cont cs
lexer cont ('{':'-':cs) = lexerEatComment 0 cont cs
lexer cont ('-':'-':cs) = lexerEatToNewline cont cs
lexer cont ('(':cs) = cont TokenOB cs
lexer cont (')':cs) = cont TokenCB cs
lexer cont ('{':c:cs) 
    | isAlpha c || c=='_' = lexBrackVar cont (c:cs)
lexer cont ('{':cs) = cont TokenOCB cs
lexer cont ('}':cs) = cont TokenCCB cs
lexer cont ('[':cs) = cont TokenOSB cs
lexer cont (']':cs) = cont TokenCSB cs
lexer cont ('?':'=':cs) = cont TokenMightEqual cs
lexer cont (';':cs) = cont TokenSemi cs
lexer cont ('\\':cs) = cont TokenLambda cs
lexer cont ('#':cs) = cont TokenType cs
lexer cont (',':cs) = cont TokenComma cs
lexer cont ('|':'(':cs) = cont TokenLazyBracket cs
lexer cont ('%':cs) = lexSpecial cont cs
lexer cont ('?':cs) = lexMeta cont cs
lexer cont (c:cs) | isOpPrefix c = lexOp cont (c:cs)
lexer cont (c:cs) = lexError c cs

lexError c s l ops = failP (show l ++ ": Unrecognised token '" ++ [c] ++ "'\n") s l ops

lexerEatComment nls cont ('-':'}':cs)
    = \fn line -> lexer cont cs fn (line+nls)
lexerEatComment nls cont ('\n':cs) = lexerEatComment (nls+1) cont cs
lexerEatComment nls cont (c:cs) = lexerEatComment nls cont cs

lexerEatToNewline cont ('\n':cs)
   = \fn line -> lexer cont cs fn (line+1)
lexerEatToNewline cont []
   = \fn line -> lexer cont [] fn line
lexerEatToNewline cont (c:cs) = lexerEatToNewline cont cs

lexNum cont cs = case readNum cs of
                    (num,rest,isreal) ->
                        cont (tok num isreal) rest
  where tok num isreal | isreal = TokenFloat (read num)
                       | otherwise = TokenInt (read num)

readNum :: String -> (String,String,Bool)
readNum x = rn' False "" x
  where rn' dot acc [] = (acc,[],dot)
        rn' False acc ('.':xs) | head xs /= '.' = rn' True (acc++".") xs
        rn' dot acc (x:xs) | isDigit x = rn' dot (acc++[x]) xs
        rn' dot acc ('e':'+':xs) = rn' True (acc++"e+") xs
        rn' dot acc ('e':'-':xs) = rn' True (acc++"e-") xs
        rn' dot acc ('e':xs) = rn' True (acc++"e") xs
        rn' dot acc xs = (acc,xs,dot)

lexString cont cs =
   \fn line ops ->
   case getstr cs of
      Just (str,rest,nls) -> cont (TokenString str) rest fn (nls+line) ops
      Nothing -> failP (fn++":"++show line++":Unterminated string contant")
                    cs fn line ops

lexChar cont cs =
   \fn line ops ->
   case getchar cs of
      Just (str,rest) -> cont (TokenChar str) rest fn line ops
      Nothing ->
          failP (fn++":"++show line++":Unterminated character constant")
                       cs fn line ops

isAllowed c = isAlpha c || isDigit c || c `elem` "_\'?#"

lexVar cont cs =
   case span isAllowed cs of
-- Keywords
      ("proof",rest) -> cont TokenProof rest
      ("data",rest) -> cont TokenDataType rest
      ("using",rest) -> cont TokenUsing rest
      ("noElim",rest) -> cont TokenNoElim rest
      ("collapsible",rest) -> cont TokenCollapsible rest
      ("where",rest) -> cont TokenWhere rest
      ("with",rest) -> cont TokenWith rest
      ("partial",rest) -> cont TokenPartial rest
      ("syntax",rest) -> cont TokenSyntax rest
      ("lazy",rest) -> cont TokenLazy rest
      ("infix",rest) -> cont TokenInfix rest
      ("infixl",rest) -> cont TokenInfixL rest
      ("infixr",rest) -> cont TokenInfixR rest
-- Types
      ("Int",rest) -> cont TokenIntType rest
      ("Char",rest) -> cont TokenCharType rest
      ("Float",rest) -> cont TokenFloatType rest
      ("String",rest) -> cont TokenStringType rest
      ("Lock",rest) -> cont TokenLockType rest
      ("Handle",rest) -> cont TokenHandleType rest
      ("Ptr",rest) -> cont TokenPtrType rest
      ("refl",rest) -> cont TokenRefl rest
      ("include",rest) -> cont TokenInclude rest
      ("do",rest) -> cont TokenDo rest
      ("if",rest) -> cont TokenIf rest
      ("then",rest) -> cont TokenThen rest
      ("else",rest) -> cont TokenElse rest
      ("let",rest) -> cont TokenLet rest
      ("in",rest) -> cont TokenIn rest
-- values
-- expressions
      (var,rest) -> cont (mkname var) rest

lexOp cont cs = case span isOpChar cs of
                   (":",rest) -> cont TokenColon rest
--                   ("+",rest) -> cont TokenPlus rest
                   ("-",rest) -> cont TokenMinus rest
--                   ("*",rest) -> cont TokenTimes rest
--                   ("/",rest) -> cont TokenDivide rest
                   ("=",rest) -> cont TokenEquals rest
--                   ("==",rest) -> cont TokenEQ rest
--                   (">",rest) -> cont TokenGT rest
--                   ("<",rest) -> cont TokenLT rest
--                   (">=",rest) -> cont TokenGE rest
--                   ("<=",rest) -> cont TokenLE rest
--                   ("++",rest) -> cont TokenConcat rest
--                   ("&&",rest) -> cont TokenAnd rest
                   ("&",rest) -> cont TokenTuple rest
--                   ("||",rest) -> cont TokenOr rest
                   ("...",rest) -> cont TokenEllipsis rest
                   ("|",rest) -> cont TokenBar rest
                   ("!",rest) -> cont TokenBang rest
                   ("->", rest) -> cont TokenArrow rest
                   ("=>", rest) -> cont TokenFatArrow rest
                   ("<-", rest) -> cont TokenLeftArrow rest
                   (op,rest) -> cont (TokenInfixName op) rest

isOpPrefix c = c `elem` ":+-*/=_.?|&><!@$%^"
isOpChar = isOpPrefix

lexBrackVar cont cs =
    case span isAllowed cs of
      (var,rest) -> cont (TokenBrackName (UN var)) rest

lexSpecial cont cs =
    case span isAllowed cs of
      ("latex",rest) -> cont TokenLaTeX rest
      ("nocg",rest) -> cont TokenNoCG rest
      ("eval",rest) -> cont TokenEval rest
      ("include",rest) -> cont TokenCInclude rest
      ("lib",rest) -> cont TokenCLib rest
-- tactics
-- FIXME: it'd be better to have a 'theorem proving' state so that these
-- don't need the ugly syntax...
      ("intro",rest) -> cont TokenIntro rest
      ("refine",rest) -> cont TokenRefine rest
      ("generalise",rest) -> cont TokenGeneralise rest
      ("refl",rest) -> cont TokenReflP rest
      ("rewrite",rest) -> cont TokenRewrite rest
      ("rewriteall",rest) -> cont TokenRewriteAll rest
      ("compute",rest) -> cont TokenCompute rest
      ("unfold",rest) -> cont TokenUnfold rest
      ("undo",rest) -> cont TokenUndo rest
      ("induction",rest) -> cont TokenInduction rest
      ("fill", rest) -> cont TokenFill rest
      ("trivial", rest) -> cont TokenTrivial rest
      ("mktac", rest) -> cont TokenMkTac rest
      ("believe", rest) -> cont TokenBelieve rest
      ("use", rest) -> cont TokenUse rest
      ("decide", rest) -> cont TokenDecide rest
      ("abandon", rest) -> cont TokenAbandon rest
      ("qed", rest) -> cont TokenQED rest
      (thing,rest) -> lexError '%' rest

-- Read everything up to '[whitespace]Qed'
{-
lexProof cont cs = 
   \fn line ->
      case getprf cs of
        Just (str,rest,nls) -> cont (TokenProof str) rest fn (nls+line)
        Nothing -> failP (fn++":"++show line++":No QED in Proof")
                          cs fn line
-}

lexMeta cont cs =
    case span isAllowed cs of
      (thing,rest) -> cont (TokenMetavar (UN thing)) rest

mkname :: String -> Token
mkname c = TokenName (UN c)

getstr :: String -> Maybe (String,String,Int)
getstr cs = case getstr' "" cs 0 of
               Just (str,rest,nls) -> Just (reverse str,rest,nls)
               _ -> Nothing
getstr' acc ('\"':xs) = \nl -> Just (acc,xs,nl)
getstr' acc ('\\':'n':xs) = getstr' ('\n':acc) xs -- Newline
getstr' acc ('\\':'r':xs) = getstr' ('\r':acc) xs -- CR
getstr' acc ('\\':'t':xs) = getstr' ('\t':acc) xs -- Tab
getstr' acc ('\\':'b':xs) = getstr' ('\b':acc) xs -- Backspace
getstr' acc ('\\':'a':xs) = getstr' ('\a':acc) xs -- Alert
getstr' acc ('\\':'f':xs) = getstr' ('\f':acc) xs -- Formfeed
getstr' acc ('\\':'0':xs) = getstr' ('\0':acc) xs -- null
getstr' acc ('\\':x:xs) = getstr' (x:acc) xs -- Literal
getstr' acc ('\n':xs) = \nl ->getstr' ('\n':acc) xs (nl+1) -- Count the newline
getstr' acc (x:xs) = getstr' (x:acc) xs
getstr' _ _ = \nl -> Nothing

getchar :: String -> Maybe (Char,String)
getchar ('\\':'n':'\'':xs) = Just ('\n',xs) -- Newline
getchar ('\\':'r':'\'':xs) = Just ('\r',xs) -- CR
getchar ('\\':'t':'\'':xs) = Just ('\t',xs) -- Tab
getchar ('\\':'b':'\'':xs) = Just ('\b',xs) -- Backspace
getchar ('\\':'a':'\'':xs) = Just ('\a',xs) -- Alert
getchar ('\\':'f':'\'':xs) = Just ('\f',xs) -- Formfeed
getchar ('\\':'0':'\'':xs) = Just ('\0',xs) -- null
getchar ('\\':x:'\'':xs) = Just (x,xs) -- Literal
getchar (x:'\'':xs) = Just (x,xs)
getchar _ = Nothing

getprf :: String -> Maybe (String, String, Int)
getprf s = case getprf' "" s 0 of 
               Just (str,rest,nls) -> Just (reverse str,rest,nls)
               _ -> Nothing
getprf' acc (c:'Q':'E':'D':rest)
    | isSpace c = \nl -> Just (acc,rest,nl)
getprf' acc ('\n':xs) = \nl ->getprf' ('\n':acc) xs (nl+1) -- Count the newline
getprf' acc (x:xs) = getprf' (x:acc) xs
getprf' acc _ = \nl -> Nothing
