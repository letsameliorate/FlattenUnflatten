{-|
    Definition for the language used in this transformation.
    Defines the distilled form.
|-}
type FreeVar = String -- Free Variable
type BoundVar = Int -- de Bruijn Index for Bound Variable
type ConName = String -- Constructor Name
type FunName = String -- Function Name
type CaseSel = (FreeVar, [DTerm]) -- Case Selector
type Branch = (ConName, [FreeVar], DTerm) -- Case Branch
type FunDef = (FunName, [FreeVar], DTerm) -- Function Definition

data DTerm = DFreeVarApp FreeVar [DTerm] -- Free Variable Application
           | DBoundVarApp BoundVar [DTerm] -- Bound Variable Application
           | DConApp ConName [DTerm] -- Constructor Application
           | DLambda FreeVar DTerm -- Lambda Abstraction
--           | DFunApp FunName [Either FreeVar BoundVar] -- Function Application
           | DFunApp FunName [DTerm] -- Function Application
           | DLet FreeVar DTerm DTerm -- Let Expression
           | DCase CaseSel [Branch] -- Case Expression
--           | DWhere FunName [DTerm] [DTerm] -- Local Function Definition
           | DWhere FunName [DTerm] FunDef -- Local Function Definition
  deriving (Show)


{-|
    Definition for the generic data type used in this transformation.
|-}
type TypeName = String -- Type Name
type TypeVar = String -- Type Variable
type TypeCon = ConName -- Type Constructor
type TypeComp = DataType -- Type Component

data DataType = DataType TypeName [TypeVar] [(TypeCon, [TypeComp])] -- Data Type
  deriving (Show, Eq)


{-|
filterNonInductiveBinders :: [DataType] -> (ConName, [FreeVar]) -> (Typename, [TypeVar], [(TypeCon, [TypeComp])]) -> [FreeVar]
-- decide / fix gamma, FreeVars, arguments for notElem, and return type
-- also decide if phi is indices or free vars
filterNonInductiveBinders gamma (c, fvs) (tname, tvars, tcons) = let (tcon, tcomps) = filter (\(tcon, tcomps) -> tcon == c) tcons
                                                                     pairs = zip fvs tcomps
                                                                     fvs' = fst . unzip . filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs
                                                                 in fvs'

getNonInductiveBinders :: [parallelisable data type instances] -> Constructor name from pattern -> [binders from pattern] -> [non-inductive binders from pattern]
getNonInductiveBinders :: [DataType] -> ConName -> [FreeVar] -> [FreeVar]
getNonInductiveBinders gamma c fvs = let tcomps = concatMap (getTypeComponents c) gamma --to get the list of type components for this constructor
                                         pairs = zip fvs tcomps -- pairs :: [(FreeVar, TypeComp)]
                                         nonInductiveBinders = (fst . unzip) (filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs)
                                     in nonInductiveBinders

getTypeComponents :: ConName -> DataType -> [TypeComp]
getTypeComponents c (DataType tname tvars tcontcomps) c = snd (filter (\(tcon, tcomps) -> tcon == c) tcontcomps)
|-}
-- getNonInductiveBinders :: [parallelisable data type instances] -> Constructor name from pattern -> [binders from pattern] -> [non-inductive binders from pattern]
getNonInductiveBinders :: [DataType] -> ConName -> [FreeVar] -> [FreeVar]
getNonInductiveBinders gamma c fvs = let tcomps = concatMap (getTypeComponents c) gamma --to get the list of type components for this constructor
                                         pairs = zip fvs tcomps -- pairs :: [(FreeVar, TypeComp)]
                                         nonInductiveBinders = (fst . unzip) (filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs)
                                     in nonInductiveBinders

getTypeComponents :: ConName -> DataType -> [TypeComp]
getTypeComponents c (DataType tname tvars tcontcomps) = (snd . head) (filter (\(tcon, tcomps) -> tcon == c) tcontcomps)




{-|
    Generates the definition for flatten and the new constructors for the Flat Data Type.
|-}
generateFlatten :: DTerm -> ([ConName], DTerm)
generateFlatten dt = ruleA1 [] [] [] dt


{-|
    Definition for transformation rule A1.
|-}
-- ruleA1 :: [Non-inductive Components] -> [New Flat Constructors] -> Flat Term -> ([New Flat Constructors], Flat Term)
ruleA1 :: [FreeVar] -> [ConName] -> [FreeVar] -> DTerm -> ([ConName], DTerm)
ruleA1 phi cs fvs (DFreeVarApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                         in applyRuleA2ForArguments cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 phi cs fvs (DBoundVarApp i dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                         in applyRuleA2ForArguments cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 phi cs fvs (DConApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                     in applyRuleA2ForArguments cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 phi cs fvs (DLambda fv dt) = let fv' = rename fvs fv
                                        (cs', dt') = ruleA1 phi cs (fv':fvs) (subst (DFreeVarApp fv []) dt)
                                    in (cs', DLambda fv (abstract fv' dt'))

ruleA1 phi cs fvs (DFunApp f dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                    in (cs', DFunApp "(++)" [(DConApp (head cs') (toDFreeVarApps phi)) , (DFunApp ("flatten_" ++ f) (concatMap free dts))])

ruleA1 phi cs fvs (DLet fv dt0 dt1) = ruleA1 phi cs fvs (subst dt0 dt1)

ruleA1 phi cs fvs (DCase csel bs) = let (cs', bs') = applyRuleA1ForBranches phi cs fvs bs []
                                    in (cs', (DCase csel bs'))

ruleA1 phi cs fvs1 (DWhere f1 dts (f2, fvs2, dt)) = let fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2
                                                        fvs2' = take (length fvs2) fvs1'
                                                        (cs', dt') = ruleA1 phi cs fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2')
                                                        dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                    in (cs', (DWhere ("flatten_" ++ f1) dts (("flatten_" ++ f2), fvs2, dt'')))


{-|
    Definition for transformation rule A2.
|-}
ruleA2 :: [ConName] -> [FreeVar] -> DTerm -> ([ConName], DTerm)
ruleA2 cs fvs (DFreeVarApp fv dts) = applyRuleA2ForArguments cs fvs (DConApp "[]" []) dts
ruleA2 cs fvs (DBoundVarApp i dts) = applyRuleA2ForArguments cs fvs (DConApp "[]" []) dts
ruleA2 cs fvs (DConApp c dts) = applyRuleA2ForArguments cs fvs (DConApp "[]" []) dts
ruleA2 cs fvs (DLambda fv dt) = let fv' = rename fvs fv
                                    (cs', dt') = ruleA2 cs (fv' : fvs) (subst (DFreeVarApp fv []) dt)
                                in (cs', DLambda fv (abstract fv' dt'))
ruleA2 cs fvs (DFunApp f dts) = (cs, (DFunApp ("flatten_" ++ f) (concatMap free dts)))
ruleA2 cs fvs (DLet fv dt0 dt1) = ruleA2 cs fvs (subst dt0 dt1)
ruleA2 cs fvs dt = ruleA1 [] cs fvs dt


{-|
    Function to sequentally apply function ruleA1.
    Used for the branch expressions in case expressions.
|-}
applyRuleA1ForBranches :: [FreeVar] -> [ConName] -> [FreeVar] -> [Branch] -> [Branch] -> ([ConName], [Branch])
applyRuleA1ForBranches phi cs fvs [] bs' = (cs, bs')
applyRuleA1ForBranches phi cs fvs1 ((c, fvs2, dt) : bs) bs' = let phi' = phi ++ (getNonInductiveBinders [] c fvs2)
                                                                  fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2
                                                                  fvs2' = take (length fvs2) fvs1'
                                                                  (cs', dt') = ruleA1 phi' cs fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2')
                                                                  dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                              in applyRuleA1ForBranches phi cs' fvs1 bs (bs' ++ [(c, fvs2, dt'')])


{-|
    Function to sequentially apply function ruleA2.
    Used for the arguments of variable and constructor applications.
|-}
applyRuleA2ForArguments :: [ConName] -> [FreeVar] -> DTerm -> [DTerm] -> ([ConName], DTerm)
applyRuleA2ForArguments cs fvs ft [] = (cs, ft)
applyRuleA2ForArguments cs fvs ft (dt:dts) = let (cs', dt') = ruleA2 cs fvs dt
                                             in applyRuleA2ForArguments cs' fvs (DFunApp "(++)" [ft, dt']) dts


{-|
    Function to add a new constructor name for the flat data type.
|-}
addFlatConName :: [ConName] -> [ConName]
addFlatConName [] = ["flatCon"]
addFlatConName cs = addFlatConName' cs (head cs)
addFlatConName' cs c = if c `elem` cs
                       then addFlatConName' cs (c ++ "'")
                       else (c : cs)


{-|
    Function to convert Free Variable Names to Free Variable Applications.
    Used for the non-inductive components that are arguments to a new constructor for the flat data type.
|-}
toDFreeVarApps :: [FreeVar] -> [DTerm]
toDFreeVarApps fvs = map (\fv -> (DFreeVarApp fv [])) fvs


{-|
    Function to create a fresh free variable not in fvs.
    fv = seed, fvs = list of free variables.
|-}
rename :: [FreeVar] -> FreeVar -> FreeVar
rename fvs fv = if fv `elem` fvs
                then rename fvs (fv ++ "'")
                else fv


{-|
    Function to substitute dt0 in dt1.
|-}
subst :: DTerm -> DTerm -> DTerm
subst dt0 dt1 = subst' 0 dt0 dt1

subst' :: Int -> DTerm -> DTerm -> DTerm
subst' i dt0 (DFreeVarApp fv dts) = dt0
subst' i dt0 (DBoundVarApp j dts) = dt0
subst' i dt0 (DConApp c dts) = dt0
subst' i dt0 (DFunApp f dts) = dt0
subst' i dt0 (DLet fv dt1 dt2) = dt0
subst' i dt0 (DCase csel bs) = dt0
subst' i dt0 (DWhere f1 dts (f2, fvs, dt)) = dt0


{-|
    Function to abstract the free variable fv in dt with its De Bruijn index.
|-}
abstract :: FreeVar -> DTerm -> DTerm
abstract fv dt = abstract' 0 fv dt

abstract' :: Int -> FreeVar -> DTerm -> DTerm
abstract' i fv dt@(DFreeVarApp fv1 dts) = dt
abstract' i fv dt@(DBoundVarApp j dts) = dt
abstract' i fv dt@(DConApp c dts) = dt
abstract' i fv dt@(DFunApp f dts) = dt
abstract' i fv dt@(DLet fv1 dt1 dt2) = dt
abstract' i fv dt@(DCase csel bs) = dt
abstract' i fv dt@(DWhere f1 dts (f2, fvs, dt2)) = dt


{-|
    Function to get the free variables in dt.
|-}
free :: DTerm -> [DTerm]
free dt = free' [] dt

free' :: [DTerm] -> DTerm -> [DTerm]
free' xs (DFreeVarApp fv dts) = xs
free' xs (DBoundVarApp i dts) = xs
free' xs (DConApp c dts) = xs
free' xs (DFunApp f dts) = xs
free' xs (DLet fv dt1 dt2) = xs
free' xs (DCase csel bs) = xs
free' xs (DWhere f1 dts (f2, fvs, dt2)) = xs