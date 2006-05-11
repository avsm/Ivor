> module Ivor.CodegenC where

Spit out C. I think this is write-only code...

> import Ivor.Bytecode
> import Ivor.SC

Some useful gadgets

> getTag :: ByteDef -> SCName -> String
> getTag scs n = case lookup n scs of
>		    Just (FI _ _ tag _ _) -> tag
>	            Nothing -> error "Can't happen (getTag)"

> getCName :: ByteDef -> SCName -> String
> getCName scs n = case lookup n scs of
>		      Just (FI _ cname _ _ _) -> cname
>	              Nothing -> error "Can't happen (getTag)"

Make the module's eval function, which checks the function tag on the
closure it is passed, and runs the appropriate function.

> mkEval :: ByteDef -> String
> mkEval scs = evalHead ++ "\n" ++ concat (map (mke'.snd) scs) ++ evalTail
>   where
>     evalHead = "VAL eval(VAL x) {" ++
>                "\n    if (x->ty != FUN) return x;" ++
>                "\n    else {" ++
>	         "\n        function* f = (function*)(x -> info);" ++
>	         "\n        switch(f->ftag) {"
>     evalTail = "        }" ++
>	         "\n    }" ++
>		 "\n    return x;" ++
>		 "\n}\n"

>     mke' (FI _ name tag arity _) = "            EVALCASE("++tag++","++
>			             show arity ++ "," ++ name ++ "("
>				     ++ showargs arity ++ "));\n"
>     showargs 0 = ""
>     showargs 1 = "FARG(0)"
>     showargs (n+1) = showargs n ++ "," ++ "FARG("++show n++")"

Make the header, including definitions of all the function tags and
function prototypes.

> mkHeaders :: ByteDef -> String
> mkHeaders scs = fileHeader ++ concat (map (mkh'.snd) scs)
>   where fileHeader = "#include \"closure.h\"\n"++
>	               "#include <stdio.h>\n\n"

>         mkh' (FI _ name tag arity tagid) =
>            "#define "++ tag ++ " " ++ show tagid ++"\n" ++
>	     "VAL "++ name ++ "(" ++ showargs arity ++");\n"
>	  showargs 0 = ""
>         showargs 1 = "VAL v0"
>         showargs (n+1) = showargs n ++ "," ++ "VAL v"++show n

Output C code for each supercombinator.

> mkCode :: ByteDef -> String
> mkCode scs = concat (map (mhc'.snd) scs)
>   where mhc' (FI bc name _ arity _) = 
>            let code = writeCode scs bc in
>	     "VAL "++ name ++ "(" ++ showargs arity ++") {\n"
>	      ++ "\n" ++ code ++ "}\n\n"

>         declaretmps 0 = "VAL tmp0;"
>         declaretmps (n+1) = declaretmps n ++ "\nVAL tmp" ++ show (n+1) ++";"
>	  showargs 0 = ""
>         showargs 1 = "VAL v0"
>         showargs (n+1) = showargs n ++ "," ++ "VAL v"++show n


> writeCode :: ByteDef -> Bytecode -> String
> writeCode scs [] = ""
> writeCode scs (c:cs) = "    " ++ wc c ++ "\n" ++ writeCode scs cs
>   where wc (STARTFN _ _) = "VAL* args;"
>         wc (DECLARE i) = "VAL v"++show i++";"
>         wc (TMP i) = "VAL tmp"++show i++";"
>         wc (RETURN i) = "return tmp"++show i++";"
>	  wc (CALL t n vs) = "tmp"++show t++ " = "++ getCName scs n ++
>		             "(" ++ showargs vs ++ ");"
>         wc (CON t tag as) 
>             | length as == 0 =
>		 "tmp"++show t++ " = MKCON0("++show tag++");"
>             | length as < 2 =
>		 "tmp"++show t++ " = MKCON"++show (length as)++
>		      "("++show tag++"," ++ showargs as++");"
>	      | otherwise = "args = MKARGS(" ++ show (length as) ++ 
>		    ");\n    " ++ mkargs as 0 ++ "tmp"++show t++ 
>		    " = MKCONN("++show tag ++",args,"++show (length as)++");"
>         wc (CLOSURE t n as) 
>             | length as == 0 = 
>	              "tmp"++show t++ " = CLOSURE0("++
>		      getTag scs n++","++show (length as)++");"
>             | length as < 6 = 
>	              "tmp"++show t++ " = CLOSURE"++show (length as)++
>		      "("++getTag scs n++","++show (length as)++","++showargs as++");"
>	      | otherwise = "args = MKARGS(" ++ show (length as) ++ 
>		      ");\n    " ++ mkargs as 0 ++ "tmp"++show t++
>		    " = CLOSUREN("++getTag scs n ++","++show (length as)++",args,"++ 
>		    show (length as)++");"
>	  wc (VAR t i) = "tmp"++show t++" = v" ++ show i ++ ";"
>         wc (GETARG t i v) = "tmp"++show t++" = GETCONARG(tmp"++show v++","
>		              ++show i++");"
>         wc (CLOSUREADD t tf as) 
>             | length as < 6 = "tmp"++show t++ " = CLOSUREADD"++
>			          show (length as)++"(tmp"++show tf++","++
>			          showargs as++");"
>	      | otherwise = "args = MKARGS(" ++ show (length as) ++ 
>		      ");\n    " ++ mkargs as 0 ++ "tmp"++show t++
>		    " = CLOSUREADDN(tmp"++ show tf ++",args,"++ 
>		    show (length as)++");"
>         wc (EVAL i) = "eval(v" ++ show i ++");"
>         wc (EVALTMP i) = "eval(tmp" ++ show i ++");"
>         wc (TYPE t) = "tmp"++show t++" = MKTYPE;"
>         wc (TAILCALL n vs) = "return "++getCName scs n ++ "(" ++ showargs vs ++ ");"
>	  wc (ALET i t) = "v"++show i++" = tmp"++show t++";"
>         wc (CASE v cs) = "switch(TAG(v"++show v++")) {\n" ++
>		   cc cs 0 ++ "    }"

>         cc [] i = "    default:\n    return NULL;\n"
>         cc (c:cs) i = "    case "++show i++":\n" ++
>		writeCode scs c ++ "\n" ++ cc cs (i+1)

>         mkargs [] _ = ""
>	  mkargs (a:as) i = "args["++show i++"] = tmp"++show a ++ ";"
>		            ++ "\n    " ++ mkargs as (i+1)

>         showargs [] = ""
>         showargs [x] = "tmp"++show x
>         showargs (x:xs) = "tmp"++show x++","++showargs xs

 writeCode bc t [] = ("",t)
 writeCode bc tmp (c:cs) = let (code,tmp') = opc tmp c
			        (code',tmp'') = writeCode bc tmp' cs in
			("\t" ++ code ++ "\n" ++ code', tmp'')
    where opc t (STARTFN _ _) = ("VAL* args;",t)
          opc t (DECLARE x) = ("VAL v"++show x++";",t)
          opc t (RETURN e) = let (code,tmp') = ecomp (t+1) e in
			       (code ++ "return t"++show t,tmp')
	   opc t (TAILCALL n es) 
                 = let (code,tmp',ts) = argcode (t+1) es [] "" in
              (code ++ "return "++ getCName bc n ++ "(" ++ arglist ts ++ ")",tmp')
          opc t (ALET x e) = error "Not done Let yet"
          opc t (CASE e es) = ("CASE foo;",t)
          ecomp t e = ("expression",t)
              | length es < 2 = "MKCON"++show (length es)++"("++show t++","++
			         argcode es++")"
              | otherwise = mkArgList (length es) ++ "MKCONN("++show t++
		             ",args,"++length es++");"
		             

          argcode t [] l code = (code,t,l)
	   argcode t (e:es) as c
               = let (ecode,t') = ecomp (t+1) e
		      code = "tmp"++show t++ " = " ++ ecode ++ ";" in
		    argcode t' es (t:as) (c++code)
          arglist [] = ""
          arglist [e] = "tmp"++show e
          arglist (e:es) = arglist es ++ "," ++ "tmp"++show e
