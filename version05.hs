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
--           | DWhere FunName [DTerm] [(FunName, DTerm)] -- Local Function Definition
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
  deriving (Show)

instance Eq DataType where
  (==) (DataType tname1 _ _) (DataType tname2 _ _) = tname1 == tname2


{-|
    Generates the definition for flatten and the new constructors for the Flat Data Type.
|-}
generateFlatten :: [DataType] -> DTerm -> ([ConName], DTerm)
generateFlatten gamma dt = ruleA1 gamma [] [] [] dt


{-|
    Definition for transformation rule A1.
|-}
-- ruleA1 :: [Parallelisable Data Types] -> [Non-inductive Components] -> [New Flat Constructors] -> [Free Variables] -> Term to Transform -> ([New Flat Constructors], Flat Term)
ruleA1 :: [DataType] -> [FreeVar] -> [ConName] -> [FreeVar] -> DTerm -> ([ConName], DTerm)
ruleA1 gamma phi cs fvs (DFreeVarApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                               in applyRuleA2ForArguments gamma cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 gamma phi cs fvs (DBoundVarApp i dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                               in applyRuleA2ForArguments gamma cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 gamma phi cs fvs (DConApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                           in applyRuleA2ForArguments gamma cs' fvs (DConApp (head cs') (toDFreeVarApps phi)) dts

ruleA1 gamma phi cs fvs (DLambda fv dt) = let fv' = rename fvs fv
                                              (cs', dt') = ruleA1 gamma phi cs (fv':fvs) (subst (DFreeVarApp fv []) dt)
                                          in (cs', DLambda fv (abstract fv' dt'))

ruleA1 gamma phi cs fvs (DFunApp f dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                          in (cs', DFunApp "(++)" [(DConApp (head cs') (toDFreeVarApps phi)) , (DFunApp ("flatten_" ++ f) (toDFreeVarApps (concatMap free dts)))])

ruleA1 gamma phi cs fvs (DLet fv dt0 dt1) = ruleA1 gamma phi cs fvs (subst dt0 dt1)

ruleA1 gamma phi cs fvs (DCase csel bs) = let (cs', bs') = applyRuleA1ForBranches gamma phi cs fvs bs []
                                          in (cs', (DCase csel bs'))

ruleA1 gamma phi cs fvs1 (DWhere f1 dts (f2, fvs2, dt)) = let fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2
                                                              fvs2' = take (length fvs2) fvs1'
                                                              (cs', dt') = ruleA1 gamma phi cs fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2')
                                                              dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                          in (cs', (DWhere ("flatten_" ++ f1) dts (("flatten_" ++ f2), fvs2, dt'')))


{-|
    Definition for transformation rule A2.
|-}
ruleA2 :: [DataType] -> [ConName] -> [FreeVar] -> DTerm -> ([ConName], DTerm)
ruleA2 gamma cs fvs (DFreeVarApp fv dts) = applyRuleA2ForArguments gamma cs fvs (DConApp "[]" []) dts
ruleA2 gamma cs fvs (DBoundVarApp i dts) = applyRuleA2ForArguments gamma cs fvs (DConApp "[]" []) dts
ruleA2 gamma cs fvs (DConApp c dts) = applyRuleA2ForArguments gamma cs fvs (DConApp "[]" []) dts
ruleA2 gamma cs fvs (DLambda fv dt) = let fv' = rename fvs fv
                                          (cs', dt') = ruleA2 gamma cs (fv' : fvs) (subst (DFreeVarApp fv []) dt)
                                      in (cs', DLambda fv (abstract fv' dt'))
ruleA2 gamma cs fvs (DFunApp f dts) = (cs, (DFunApp ("flatten_" ++ f) (toDFreeVarApps (concatMap free dts))))
ruleA2 gamma cs fvs (DLet fv dt0 dt1) = ruleA2 gamma cs fvs (subst dt0 dt1)
ruleA2 gamma cs fvs dt = ruleA1 gamma [] cs fvs dt


{-|
    Function to sequentally apply function ruleA1.
    Used for the branch expressions in case expressions.
|-}
applyRuleA1ForBranches :: [DataType] -> [FreeVar] -> [ConName] -> [FreeVar] -> [Branch] -> [Branch] -> ([ConName], [Branch])
applyRuleA1ForBranches gamma phi cs fvs [] bs' = (cs, bs')
applyRuleA1ForBranches gamma phi cs fvs1 ((c, fvs2, dt) : bs) bs' = let phi' = phi ++ (getNonInductiveBinders gamma c fvs2)
                                                                        fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2
                                                                        fvs2' = take (length fvs2) fvs1'
                                                                        (cs', dt') = ruleA1 gamma phi' cs fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2')
                                                                        dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                                    in applyRuleA1ForBranches gamma phi cs' fvs1 bs (bs' ++ [(c, fvs2, dt'')])


{-|
    Function to sequentially apply function ruleA2.
    Used for the arguments of variable and constructor applications.
|-}
applyRuleA2ForArguments :: [DataType] -> [ConName] -> [FreeVar] -> DTerm -> [DTerm] -> ([ConName], DTerm)
applyRuleA2ForArguments gamma cs fvs ft [] = (cs, ft)
applyRuleA2ForArguments gamma cs fvs ft (dt:dts) = let (cs', dt') = ruleA2 gamma cs fvs dt
                                                   in applyRuleA2ForArguments gamma cs' fvs (DFunApp "(++)" [ft, dt']) dts


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
subst' i dt0 (DFreeVarApp fv dts) = DFreeVarApp fv (map (subst' i dt0) dts)
subst' i dt0 (DBoundVarApp j dts) = dt0
subst' i dt0 (DConApp c dts) = DConApp c (map (subst' i dt0) dts)
subst' i dt0 (DLambda fv dt) = DLambda fv (subst' (i+1) dt0 dt)
subst' i dt0 (DFunApp f dts) = DFunApp f (map (subst' i dt0) dts)
subst' i dt0 (DLet fv dt1 dt2) = dt0
subst' i dt0 (DCase csel bs) = dt0
subst' i dt0 (DWhere f1 dts (f2, fvs, dt)) = dt0


{-|
    Function to shift De Bruijn index for substitution.
|-}
shift :: Int -> Int -> DTerm -> DTerm
shift 0 d dt = dt


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
free :: DTerm -> [FreeVar]
free dt = free' [] dt

free' :: [FreeVar] -> DTerm -> [FreeVar]
free' xs (DFreeVarApp fv dts) = foldr (\dt xs -> free' xs dt) (if fv `elem` xs then xs else fv:xs) dts
free' xs (DBoundVarApp i dts) = foldr (\dt xs -> free' xs dt) xs dts
free' xs (DConApp c dts) = foldr (\dt xs -> free' xs dt) xs dts
free' xs (DLambda fv dt) = free' xs dt
free' xs (DFunApp f dts) = foldr (\dt xs -> free' xs dt) xs dts
free' xs (DLet fv dt1 dt2) = free' (free' xs dt1) dt2
free' xs (DCase (fv, dts) bs) = foldr (\(c, fvs, dt) xs -> free' xs dt) (free' xs (DFreeVarApp fv dts)) bs
free' xs (DWhere f1 dts (f2, fvs, dt2)) = free' (free' xs (DFunApp f1 dts)) dt2


{-|
    Function to filter the non-inductive binders from a pattern.

-- getTypeComponents for c can never be [], because fvs for c is not [].
-- => filter in getTypeComponents is never []. => head is never applied on [].
-- but, c may have no non-inductive components.
-- => filter on pairs can be [].
-- but, since (fst . unzip) [] = [], fst is safe.
|-}
-- getNonInductiveBinders :: [parallelisable data type instances] -> Constructor name from pattern -> [binders from pattern] -> [non-inductive binders from pattern]
getNonInductiveBinders :: [DataType] -> ConName -> [FreeVar] -> [FreeVar]
getNonInductiveBinders gamma c [] = []
getNonInductiveBinders gamma c fvs = let tcomps = concatMap (getTypeComponents c) gamma --to get the list of type components for this constructor
                                         pairs = zip fvs tcomps -- pairs :: [(FreeVar, TypeComp)]
                                     in (fst . unzip) (filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs)
--                                         nonInductiveBinders = (fst . unzip) (filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs)
--                                     in nonInductiveBinders

getTypeComponents :: ConName -> DataType -> [TypeComp]
getTypeComponents c (DataType tname tvars tcontcomps) = (snd . head) (filter (\(tcon, tcomps) -> tcon == c) tcontcomps)