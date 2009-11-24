> module Idris.Fontlock(htmlise,latexise) where

> import Data.Char
> import Idris.AbsSyntax
> import Idris.Lexer
> import Idris.Context

> data Markup = DC | TC | FN | CM | VV | KW | ST | None
>   deriving Show

> hclass DC = "datacon"
> hclass TC = "typecon"
> hclass FN = "function"
> hclass CM = "comment"
> hclass VV = "variable"
> hclass KW = "keyword"
> hclass ST = "string"
> hclass None = ""

> mkMarkups :: Ctxt IvorFun -> [(String, Markup)]
> mkMarkups ctxt = map mkMarkup (map (\ (x,y) -> (x, rawDecl y)) (ctxtAlist ctxt))

> mkMarkup :: (Id, Decl) -> (String, Markup)
> mkMarkup (n, Fun _ _) = (show n, FN)
> mkMarkup (n, Fwd _ _ _) = (show n, FN)
> mkMarkup (n, TermDef _ _ _) = (show n, FN)
> mkMarkup (n, Prf _) = (show n, FN)
> mkMarkup (n, DataDecl _) = (show n, TC)
> mkMarkup (n, Constructor) = (show n, DC)
> mkMarkup (n, _) = (show n, VV)

> getMarkup :: String -> [(String, Markup)] -> Markup
> getMarkup x ms = case lookup x ms of
>                    Just m -> m
>                    Nothing -> VV

> markupText :: [(String, Markup)] -> String -> [(Markup, String)]
> markupText ms ('-':'-':xs) = markupCMtoNewline "" ms xs
> markupText ms ('{':'-':xs) = markupCM "" ms xs
> markupText ms ('"':xs) = markupString ms xs
> markupText ms ('%':xs) = markupSpecial ms xs
> markupText ms (c:cs)
>       | isAlpha c = markupVar ms (c:cs)
> markupText ms (c:cs) = (None, [c]):markupText ms cs

> markupText ms [] = []

> keywords = ["proof","data","using","idiom","params","namespace","module",
>             "import","export","inline","where","partial","syntax","lazy",
>             "infix","infixl","infixr","do","refl","if","then","else","let",
>             "in","return","include"]
> types = ["Int","Char","Float","Ptr","Lock","Handle"]

> markupSpecial ms cs = case span isAllowed cs of
>      (var,rest) -> (None, '%':var):(markupText ms rest)

> markupVar ms cs = case span isAllowed cs of
>      (var,rest) -> if (var `elem` keywords) 
>                       then (KW, var):(markupText ms rest)
>                       else if (var `elem` types) 
>                         then (TC, var):(markupText ms rest)
>                         else (getMarkup var ms, var):(markupText ms rest)

> markupCMtoNewline acc ms ('\n':xs) = (CM, "--"++reverse acc):
>                                        markupText ms ('\n':xs)
> markupCMtoNewline acc ms (x:xs) = markupCMtoNewline (x:acc) ms xs
> markupCMtoNewline acc ms [] = (CM, "--"++reverse acc):[]

> markupCM acc ms ('-':'}':xs) = (CM, "{-"++reverse acc++"-}"):markupText ms xs
> markupCM acc ms (x:xs) = markupCM (x:acc) ms xs
> markupCM acc ms [] = (CM, "{-"++reverse acc):[]

> markupString ms xs = case getstr xs of
>                        Just (str, rest, nls) -> (ST, show str):markupText ms rest

> htmlise :: Ctxt IvorFun -> FilePath -> FilePath -> IO ()
> htmlise ctxt fp outf = do txt <- readFile fp
>                           let ms = mkMarkups ctxt
>                           let mtxt = markupText ms txt
>                           writeFile outf (renderHTML fp mtxt)

> latexise :: Ctxt IvorFun -> FilePath -> FilePath -> IO ()
> latexise ctxt fp outf = do txt <- readFile fp
>                            let ms = mkMarkups ctxt
>                            let mtxt = markupText ms txt
>                            writeFile outf (renderLatex mtxt)

> renderHTML :: String -> [(Markup, String)] -> String
> renderHTML title ms = htmlHeader title ++ 
>                       "<pre>\n" ++ html ms ++ "\n</pre>\n\n</body></html>"
>   where 
>     html [] = ""
>     html ((None, t):xs) = t ++ html xs
>     html ((m, t):xs) = "<span class=\"" ++ hclass m ++ "\">" ++ t ++ "</span>"
>                        ++ html xs

> htmlHeader title = "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">" ++
>                    "<html><head><title>" ++ title ++ "</title>\n" ++
>                    "<style type=\"text/css\">\n" ++
>                    "." ++ hclass DC ++ " {\n  color:red\n}\n" ++ 
>                    "." ++ hclass TC ++ " {\n  color:blue\n}\n" ++ 
>                    "." ++ hclass FN ++ " {\n  color:green\n}\n" ++ 
>                    "." ++ hclass VV ++ " {\n  color:purple\n}\n" ++ 
>                    "." ++ hclass CM ++ " {\n  color:darkred\n}\n" ++ 
>                    "." ++ hclass ST ++ " {\n  color:gray\n}\n" ++ 
>                    "." ++ hclass KW ++ " {\n  color:black\n  font-weight:italic\n}\n" ++ 
>                    "</style></head>"

> renderLatex :: [(Markup, String)] -> String
> renderLatex ms = latexHeader ++ latex ms ++ "\\end{SaveVerbatim}\n\\BUseVerbatim{prog}\n\n\\end{document}"
>   where 
>     latex [] = ""
>     latex ((None, t):xs) = t ++ latex xs
>     latex ((m, t):xs) = "^" ++ show m ++ "@" ++ t ++ "!"
>                         ++ latex xs

> latexHeader = "\\documentclass[a4paper]{article}\n" ++
>   "\n\\usepackage{fancyvrb}\n\\usepackage{color}\n\n\\begin{document}\n\n" ++
>   "\\newcommand{\\" ++ show DC ++ "}[1]{\\textcolor[rgb]{0.8,0,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show TC ++ "}[1]{\\textcolor[rgb]{0,0,0.8}{#1}}\n" ++
>   "\\newcommand{\\" ++ show FN ++ "}[1]{\\textcolor[rgb]{0,0.5,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show VV ++ "}[1]{\\textcolor[rgb]{0.5,0,0.5}{#1}}\n" ++
>   "\\newcommand{\\" ++ show CM ++ "}[1]{\\textcolor[rgb]{0.4,0.2,0.2}{#1}}\n" ++
>   "\\newcommand{\\" ++ show KW ++ "}[1]{\\textcolor[rgb]{0,0,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show ST ++ "}[1]{\\textcolor[rgb]{0.4,0.4,0.4}{#1}}\n" ++
>   "\\begin{SaveVerbatim}[commandchars=^@!]{prog}\n"

