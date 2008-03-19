> module Ivor.ICompile where

> import Ivor.TTCore
> import Ivor.Datatype
> import Ivor.Nobby
> import Ivor.Gadgets

> import List
> import Debug.Trace

Structure of simple case expressions, from which we can build actual code for
elimination rules in whatever form we like, eg for NBE or compiled code.

> data SimpleCase = Case Name Int [SimpleCase] -- case x::ty of xs, x is a local var
>                 | IReduce (Indexed Name) -- Found a reduction!
>	          | Impossible -- No well-typed term can get here
>   deriving Show

Compile a set of iota schemes to simple case structure.

TMP ASSUMPTION: There is always one argument where all cases are disjoint.
We can make sure this is always the case even for detaggable/collapsible 
families, although we should do better later.

> compileSchemes :: [Scheme Name] -> SimpleCase
> compileSchemes [] = Impossible
> compileSchemes ss = icomp ss [0..(length (getPat (ss!!0)))-1]
>    where icomp ss es = let pats = transpose (map getPat ss) in
>			 let (pats',es') = unzip $ orderPatts (zip pats es) in
>			 let ss' = mangleArgOrder ss (reverse es') in
>			 let top = map schhead ss'
>			     rest = map schtail ss' in
>			 icomp' top rest es'
>          schhead (Sch x red) = (head x, red)
>          schtail (Sch x red) = Sch (tail x) red
>          icomp' x xs (e:es) | allDisjoint (map fst x) = doCase1 e x
>		              | otherwise = error "Can't find a scrutinee"
>          orderPatts = sortBy cmpPat
>          cmpPat (p,v) (p',v') = compare (numDisjoint p') (numDisjoint p)

I wish I'd written a comment here when I wrote this...

> mangleArgOrder :: [Scheme Name] -> [Int] -> [Scheme Name]
> mangleArgOrder [] _ = []
> mangleArgOrder (x:xs) es = (ma' x es):(mangleArgOrder xs es)
>    where ma' (Sch ps ired) es = Sch (reorder ps es) ired
>          reorder ps xs = foldl (\ih x -> (ps!!x):ih) [] xs

> allDisjoint ps = numDisjoint ps == length ps

> numDisjoint :: [Pattern n] -> Int
> numDisjoint [] = 0
> numDisjoint (x:xs) | x `djWith` xs = 1+(numDisjoint xs)
>	             | otherwise = numDisjoint xs
>   where djWith (PCon _ _ _ _) [] = True
>         djWith _ [] = False
>         djWith x (y:ys) | dj x y = djWith x ys
>		          | otherwise = False
>         dj (PCon x _ _ _) (PCon y _ _ _) = x /= y
>         dj _ _ = False

Case 1: All patterns are disjoint.

> doCase1 :: Int -> [(Pattern Name, Indexed Name)] -> SimpleCase
> doCase1 x ps = Case (ty ps) x (order ps)
>    where order ps = insertDefaults 
>	                  (sortBy (\ (x,y) (x',y') -> compare x x') ps)
>	   insertDefaults ps = id' 0 ps
>          id' n [] = []
>	   id' n allps@((PCon i _ _ _,t):ps) 
>             | n == i = (IReduce t):(id' (n+1) ps)
>             | otherwise = Impossible:(id' (n+1) allps)
>          ty ((PCon _ _ tyname _, _):xs) = tyname


Make an elimination rule implementation from a simple case expression.

> mkElim :: Name -> (Indexed Name) -> Int -> SimpleCase -> ElimRule
> mkElim ename ty arity cs sp | size sp /= arity = Nothing
>		              | otherwise = doElim sp cs
>   where doElim sp Impossible = Nothing
>         doElim sp (Case _ x cs) = let xval = (sp??x) in
>                    case xval of
>		      (MR (RCon tag _ _)) -> doElim sp (cs!!tag)
>		      _ -> Nothing
>         doElim sp (IReduce (Ind t)) 
>                = let recrule = mkElim ename ty arity cs
>		       gam = extend emptyGam (ename,G (ElimRule recrule) ty defplicit)
>		       red = (nf gam (VG (revlistify sp)) [] False t)
>			 in (Just red)
