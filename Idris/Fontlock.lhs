> module Idris.Fontlock(htmlise,latexise) where

> import Data.Char
> import List

> import Idris.AbsSyntax
> import Idris.Lexer
> import Idris.Context

> data Markup = DC | TC | FN | CM | VV | KW | ST | CH | LCM
>             | BRK | SEC | SUBSEC 
>             | TITLE | AUTHOR | HTML | LATEX | None
>   deriving Show

> hclass DC = "datacon"
> hclass TC = "typecon"
> hclass FN = "function"
> hclass CM = "comment"
> hclass VV = "variable"
> hclass KW = "keyword"
> hclass ST = "string"
> hclass CH = "string"
> hclass _ = ""

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
> markupText ms ('-':'-':' ':'I':'G':'N':'O':'R':'E':xs) = endIgnore ms xs
> markupText ms ('-':'-':'\n':xs) = (BRK, ""):markupText ms xs
> markupText ms ('-':'-':' ':'S':'e':'c':'t':'i':'o':'n':':':' ':xs) 
>                = markupSECtoNewline SEC "" ms xs
> markupText ms ('-':'-':' ':'T':'i':'t':'l':'e':':':' ':xs) 
>                = markupSECtoNewline TITLE "" ms xs
> markupText ms ('-':'-':' ':'L':'a':'T':'e':'X':':':' ':xs) 
>                = markupSECtoNewline LATEX "" ms xs
> markupText ms ('-':'-':' ':'H':'T':'M':'L':':':' ':xs) 
>                = markupSECtoNewline HTML "" ms xs
> markupText ms ('-':'-':' ':'A':'u':'t':'h':'o':'r':':':' ':xs) 
>                = markupSECtoNewline AUTHOR "" ms xs
> markupText ms ('-':'-':' ':'S':'u':'b':'s':'e':'c':'t':'i':'o':'n':':':' ':xs) 
>                = markupSECtoNewline SUBSEC "" ms xs
> markupText ms ('-':'-':xs) = markupCMtoNewline "" ms xs
> markupText ms ('{':'-':'>':xs) = markupText ms xs
> markupText ms ('>':'-':'}':xs) = markupText ms xs
> markupText ms ('{':'-':'-':xs) = markupLCM "" ms xs
> markupText ms ('{':'-':xs) = markupCM "" ms xs
> markupText ms ('"':xs) = markupString ms xs
> markupText ms ('\'':c:'\'':xs) = (CH, ['\'',c,'\'']):markupText ms xs
> markupText ms ('%':xs) = markupSpecial ms xs
> markupText ms ('\t':xs) = (None, "        "):markupText ms xs
> markupText ms (c:cs)
>       | isAlpha c = markupVar ms (c:cs)
> markupText ms (c:cs) = (None, [c]):markupText ms cs

> markupText ms [] = []

> keywords = ["proof","data","using","idiom","params","namespace","module",
>             "import","export","inline","where","partial","syntax","lazy",
>             "infix","infixl","infixr","do","refl","if","then","else","let",
>             "in","return","include"]
> types = ["String","Int","Char","Float","Ptr","Lock","Handle"]

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

> markupSECtoNewline sec acc ms ('\n':xs) = (sec, reverse acc):
>                                        markupText ms ('\n':xs)
> markupSECtoNewline sec acc ms (x:xs) = markupSECtoNewline sec (x:acc) ms xs
> markupSECtoNewline sec acc ms [] = (sec, reverse acc):[]

> markupCM acc ms ('-':'}':xs) = (CM, "{-"++reverse acc++"-}"):markupText ms xs
> markupCM acc ms (x:xs) = markupCM (x:acc) ms xs
> markupCM acc ms [] = (CM, "{-"++reverse acc):[]

> markupLCM acc ms ('-':'-':'}':xs) = (LCM, reverse acc):markupText ms xs
> markupLCM acc ms (x:xs) = markupLCM (x:acc) ms xs
> markupLCM acc ms [] = (LCM, reverse acc):[]

> endIgnore ms ('-':'-':' ':'S':'T':'A':'R':'T':'\n':xs) = markupText ms xs
> endIgnore ms (x:xs) = endIgnore ms xs
> endIgnore ms [] = []

> markupString ms xs = case getstr xs of
>                        Just (str, rest, nls) -> (ST, show str):markupText ms rest

> htmlise :: Ctxt IvorFun -> FilePath -> FilePath -> Maybe FilePath -> IO ()
> htmlise ctxt fp outf style 
>                      = do txt <- readFile fp
>                           let ms = mkMarkups ctxt
>                           let mtxt = markupText ms txt
>                           writeFile outf (renderHTML fp style mtxt)

> latexise :: Ctxt IvorFun -> FilePath -> FilePath -> IO ()
> latexise ctxt fp outf = do txt <- readFile fp
>                            let ms = mkMarkups ctxt
>                            let mtxt = markupText ms txt
>                            writeFile outf (renderLatex mtxt)

> skipnl :: [(Markup, String)] -> [(Markup, String)]
> skipnl ((None, "\n"):xs) = skipnl xs
> skipnl xs = xs

> skipIfBrk :: [(Markup, String)] -> [(Markup, String)]
> skipIfBrk xs = si xs xs
>    where si orig next@((BRK, _):xs) = next
>          si orig next@((TITLE, _):xs) = next
>          si orig next@((HTML, _):xs) = next
>          si orig next@((LATEX, _):xs) = next
>          si orig next@((AUTHOR, _):xs) = next
>          si orig next@((SEC, _):xs) = next
>          si orig next@((SUBSEC, _):xs) = next
>          si orig next@((LCM, _):xs) = next
>          si orig ((None, "\n"):xs) = si orig xs
>          si orig _ = orig

> renderHTML :: String -> Maybe String -> [(Markup, String)] -> String
> renderHTML title style ms = htmlHeader title style ++ 
>                       "<code>\n" ++ html (skipIfBrk ms) ++ "\n</code>\n\n</body></html>"
>   where 
>     html [] = ""
>     html ((None, "\n"):xs) = tHtml "\n" ++ html (skipIfBrk xs)
>     html ((None, t):xs) = tHtml t ++ html xs
>     html ((TITLE, t):xs) 
>        = "</code>\n\n<h2>" ++ t ++ "</h2>\n\n<code>" ++ html (skipnl xs)
>     html ((HTML, t):xs) 
>        = "</code>\n\n<p>" ++ t ++ "</p>\n\n<code>" ++ html (skipnl xs)
>     html ((LATEX, t):xs) 
>        = html (skipnl xs)
>     html ((AUTHOR, t):xs) 
>        = -- "</code>\n\n<h4>Author: " ++ t ++ "</h4>\n\n<code>" ++ 
>          "</code>" ++ sechead xs ++ "\n\n<code>" ++ html (skipnl xs)
>     html ((SEC, t):xs) 
>        = "</code><a name=\"" ++ secname t ++ "\">\n\n<h3>" ++ t ++ "</h3>\n\n<code>" ++ html (skipnl xs)
>     html ((SUBSEC, t):xs) 
>        = "</code>\n\n<h4>" ++ t ++ "</h4>\n\n<code>" ++ html (skipnl xs)
>     html ((BRK, t):xs) = tHtml t ++ html xs
>     html ((LCM, t):xs) = "</code>\n\n<p class=\"explanation\">" ++ tpara 0 t ++ "</p>\n\n<code>" ++ html (skipnl xs)
>     html ((m, t):xs) = "<span class=\"" ++ hclass m ++ "\">" ++ tHtml t ++ 
>                        "</span>" ++ html xs
>     tHtml = concat.(map th) 

>     th ' ' = "&nbsp;"
>     th '\n' = "</code><br>\n<code>"
>     th x = [x]

>     tpara l [] = ""
>     tpara l ('"':xs) = case getstr xs of
>                        Just (str,rest,_) -> "<code>" ++ tpara l str ++ "</code>" ++
>                                             tpara l rest
>                        _ -> error xs
>     tpara l ('U':'R':'L':'[':xs) =
>         case span (/=']') xs of
>           (url, ']':rest) -> "<a href=\"" ++ url ++ "\">" ++ url ++ "</a>"
>                          ++ tpara l rest
>     tpara l ('\\':'/':xs) = '/':tpara l xs 
>     tpara l ('\\':'\\':xs) = '\\':tpara l xs 
>     tpara l ('\\':'*':xs) = '*':tpara l xs 
>     tpara l ('/':xs) =
>         case span (/='/') xs of
>           (txt, '/':rest) -> "<em>" ++ txt ++ "</em>" ++ tpara l rest
>     tpara l ('*':xs) = case span (=='*') xs of
>                          (_,rest) -> "<li>" ++ tpara l rest
>     tpara l ('\n':'\n':'*':xs) = "<ul>\n" ++ tpara (l+1) ('*':xs)
>     tpara l ('\n':'\n':xs) = "\n</p>\n<p>\n" ++ tpara l xs
>     tpara l ('\n':'-':xs) = if (l>0) then "</ul>" ++ tpara (l-1) xs 
>                                       else "</p><p>" ++ tpara l xs
>     tpara l ('<':xs) = "&lt;"++ tpara l xs
>     tpara l (x:xs) = x:(tpara l xs)

> htmlHeader title style
>                = "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.01//EN\">" ++
>                  "<html><head><title>" ++ title ++ "</title>\n" ++
>                  defaultStyle style ++ "</head><body>"

> secname t = take 10 (filter isAlpha t)

> getsecs [] = []
> getsecs ((SEC,t):xs) = ("<a href=\"#" ++ (secname t) ++"\">"++ t ++ "</a>"):(getsecs xs)
> getsecs (_:xs) = getsecs xs

> sechead ms = let ss = getsecs ms in
>              if null ss then "" 
>                         else concat (intersperse " | " (getsecs ms)) ++ "<br>"

> defaultStyle Nothing 
>                  = "<style type=\"text/css\">\n" ++
>                    "." ++ hclass DC ++ " {\n  color:red; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass TC ++ " {\n  color:blue; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass FN ++ " {\n  color:green; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass VV ++ " {\n  color:purple; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass CM ++ " {\n  color:darkred; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass ST ++ " {\n  color:gray; font-family: Courier;\n}\n" ++ 
>                    "." ++ hclass KW ++ " {\n  color:black;\n  font-family: Courier; font-weight:bold;\n}\n" ++ 
>                    "p.explanation {\n  color:black;\n}\n" ++
>                    "BODY, SPAN {\n  font-family: Tahoma;\n" ++
>                    "  color:  #000020;\n  background: #f0f0f0;\n}\n" ++
>                    "</style>"
> defaultStyle (Just s) = "<link rel=\"stylesheet\" type=\"text/css\" href=\"" ++ s ++ "\">"

> renderLatex :: [(Markup, String)] -> String
> renderLatex ms = latexHeader ++ latex 0 (skipIfBrk ms) ++ "\n\n\\end{document}"
>   where 
>     latex i [] = usev i
>     latex i ((None, "\n"):xs) = "\n" ++ latex i (skipIfBrk xs)
>     latex i ((None, t):xs) = t ++ latex i xs
>     latex i ((BRK, t):xs) = usev i ++ startv (i+1) ++ latex (i+1) xs
>     latex i ((TITLE, t):xs) = "\\title{" ++ t ++ "}\n" ++ latex i (skipnl xs)
>     latex i ((HTML, t):xs) = latex i (skipnl xs)
>     latex i ((AUTHOR, t):xs) = "\\author{" ++ t ++ "}\n\\maketitle\n\n" ++ startv i ++ latex i (skipnl xs)
>     latex i ((SEC, t):xs) = usev i ++ "\\section{" ++ t ++ "}\n\n" ++ startv (i+1) ++ latex (i+1) (skipnl xs)
>     latex i ((SUBSEC, t):xs) = usev i ++ "\\subsection{" ++ t ++ "}\n\n" ++ startv (i+1) ++ latex (i+1) (skipnl xs)
>     latex i ((LCM, t):xs) = usev i ++ tpara 0 t ++ "\n\n" ++ startv (i+1) ++ latex (i+1) (skipnl xs)
>     latex i ((LATEX, t):xs) = usev i ++ tpara 0 t ++ "\n\n" ++ startv (i+1) ++ latex (i+1) (skipnl xs)
>     latex i ((m, t):xs) = "^" ++ show m ++ "@" ++ t ++ "!"
>                               ++ latex i xs

>     tpara l [] = ""
>     tpara l ('"':xs) = case getstr xs of
>                        Just (str,rest,_) -> "\\texttt{" ++ tpara l str ++ "}" ++
>                                             tpara l rest
>     tpara l ('U':'R':'L':'[':xs) =
>         case span (/=']') xs of
>           (url, ']':rest) -> "\\url{" ++ url ++ "}" ++ tpara l rest
>     tpara l ('/':'/':xs) = '/':tpara l xs
>     tpara l ('/':xs) =
>         case span (/='/') xs of
>           (txt, '/':rest) -> "\\emph{" ++ txt ++ "}" ++ tpara l rest
>           (txt, rest) -> "\\emph{" ++ txt ++ "}" ++ tpara l rest
>     tpara l ('~':xs) = "\\~{ }" ++ tpara l xs
>     tpara l ('#':xs) = "\\#" ++ tpara l xs
>     tpara l ('\n':'\n':'*':xs) = "\n\\begin{itemize}\n" ++ tpara (l+1) ('*':xs)
>     tpara l ('\n':'-':xs) = if (l>0) then "\\end{itemize}" ++ tpara (l-1) xs 
>                                       else "\n\n" ++ tpara l xs
>     tpara l ('*':xs) = case span (=='*') xs of
>                          (_,rest) -> "\\item " ++ tpara l rest
>     tpara l (x:xs) = x:(tpara l xs)

>     usev i = "\n\\end{SaveVerbatim}\n\\BUseVerbatim{vbtm" ++ show i ++ "}\n\n"
>     startv i = "\\begin{SaveVerbatim}[commandchars=^@!]{vbtm" ++ show i ++ "}\n\n"


> latexHeader = "\\documentclass[a4paper]{article}\n" ++
>   "\n\\usepackage{fancyvrb}\n\\usepackage{color}\n\\usepackage{url}\n\n\\begin{document}\n\n" ++
>   "\\newcommand{\\" ++ show DC ++ "}[1]{\\textcolor[rgb]{0.8,0,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show TC ++ "}[1]{\\textcolor[rgb]{0,0,0.8}{#1}}\n" ++
>   "\\newcommand{\\" ++ show FN ++ "}[1]{\\textcolor[rgb]{0,0.5,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show VV ++ "}[1]{\\textcolor[rgb]{0.5,0,0.5}{#1}}\n" ++
>   "\\newcommand{\\" ++ show CM ++ "}[1]{\\textcolor[rgb]{0.4,0.2,0.2}{#1}}\n" ++
>   "\\newcommand{\\" ++ show KW ++ "}[1]{\\textcolor[rgb]{0,0,0}{#1}}\n" ++
>   "\\newcommand{\\" ++ show ST ++ "}[1]{\\textcolor[rgb]{0.4,0.4,0.4}{#1}}\n"

