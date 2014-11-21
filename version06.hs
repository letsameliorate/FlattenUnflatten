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
    Generates the definition for flatten and the new (constructor, typecomponents) pairs for the Flat Data Type.
|-}
generateFlatten :: [DataType] -> DTerm -> ([(ConName, [TypeComp])], DTerm)
generateFlatten gamma dt = ruleA1 gamma ([], []) [] [] dt


{-|
    Definition for transformation rule A1.

-- ruleA1 :: [Parallelisable Data Types] 
--        -> ([Non-inductive Components], [Types for non-inductive components]) 
--        -> [(New Flat Constructor Name, [Type Components])] 
--        -> [Free Variables] 
--        -> Term to Transform 
--        -> ([(New Flat Constructor Name, [Type Components])], Flat Term)
|-}
ruleA1 :: [DataType] -> ([FreeVar], [TypeComp]) -> [(ConName, [TypeComp])] -> [FreeVar] -> DTerm -> ([(ConName, [TypeComp])], DTerm)
ruleA1 gamma (phi, tcomps) ctcomps fvs (DFreeVarApp fv dts) = let c' = newFlatConName (fst (unzip ctcomps))
                                                                  ctcomps' = (c', tcomps) : ctcomps
                                                              in applyRuleA2ForArguments gamma ctcomps' fvs (DConApp c' (toDFreeVarApps phi)) dts

ruleA1 gamma (phi, tcomps) ctcomps fvs (DBoundVarApp fv dts) = let c' = newFlatConName (fst (unzip ctcomps))
                                                                   ctcomps' = (c', tcomps) : ctcomps
                                                               in applyRuleA2ForArguments gamma ctcomps' fvs (DConApp c' (toDFreeVarApps phi)) dts

ruleA1 gamma (phi, tcomps) ctcomps fvs (DConApp fv dts) = let c' = newFlatConName (fst (unzip ctcomps))
                                                              ctcomps' = (c', tcomps) : ctcomps
                                                          in applyRuleA2ForArguments gamma ctcomps' fvs (DConApp c' (toDFreeVarApps phi)) dts

ruleA1 gamma (phi, tcomps) ctcomps fvs (DLambda fv dt) = let fv' = rename fvs fv
                                                             (ctcomps', dt') = ruleA1 gamma (phi, tcomps) ctcomps (fv':fvs) (subst (DFreeVarApp fv []) dt)
                                                         in (ctcomps', DLambda fv (abstract fv' dt'))

ruleA1 gamma (phi, tcomps) ctcomps fvs (DFunApp f dts) = let c' = newFlatConName (fst (unzip ctcomps))
                                                             ctcomps' = (c', tcomps) : ctcomps
                                                         in (ctcomps', DFunApp "(++)" [(DConApp c' (toDFreeVarApps phi)), (DFunApp ("flatten_" ++ f) (toDFreeVarApps (concatMap free dts)))])

ruleA1 gamma (phi, tcomps) ctcomps fvs (DLet fv dt0 dt1) = ruleA1 gamma (phi, tcomps) ctcomps fvs (subst dt0 dt1)

ruleA1 gamma (phi, tcomps) ctcomps fvs (DCase csel bs) = let (ctcomps', bs') = applyRuleA1ForBranches gamma (phi, tcomps) ctcomps fvs bs []
                                                         in (ctcomps', (DCase csel bs'))

ruleA1 gamma (phi, tcomps) ctcomps fvs1 (DWhere f1 dts (f2, fvs2, dt)) = let fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2
                                                                             fvs2' = take (length fvs2) fvs1'
                                                                             (ctcomps', dt') = ruleA1 gamma ([], []) ctcomps fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2') -- TBD: verify (phi, tcomps) = ([], [])
                                                                             dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                                         in (ctcomps', (DWhere ("flatten_" ++ f1) dts (("flatten_" ++ f2), fvs2, dt'')))


{-|
    Definition for transformation rule A2.
|-}
ruleA2 :: [DataType] -> [(ConName, [TypeComp])] -> [FreeVar] -> DTerm -> ([(ConName, [TypeComp])], DTerm)
ruleA2 gamma ctcomps fvs (DFreeVarApp fv dts) = applyRuleA2ForArguments gamma ctcomps fvs (DConApp "[]" []) dts
ruleA2 gamma ctcomps fvs (DBoundVarApp i dts) = applyRuleA2ForArguments gamma ctcomps fvs (DConApp "[]" []) dts
ruleA2 gamma ctcomps fvs (DConApp c dts) = applyRuleA2ForArguments gamma ctcomps fvs (DConApp "[]" []) dts
ruleA2 gamma ctcomps fvs (DLambda fv dt) = let fv' = rename fvs fv
                                               (ctcomps', dt') = ruleA2 gamma ctcomps (fv' : fvs) (subst (DFreeVarApp fv []) dt)
                                           in (ctcomps', DLambda fv (abstract fv' dt'))
ruleA2 gamma ctcomps fvs (DFunApp f dts) = (ctcomps, (DFunApp ("flatten_" ++ f) (toDFreeVarApps (concatMap free dts))))
ruleA2 gamma ctcomps fvs (DLet fv dt0 dt1) = ruleA2 gamma ctcomps fvs (subst dt0 dt1)
ruleA2 gamma ctcomps fvs dt = ruleA1 gamma ([], []) ctcomps fvs dt


{-|
    Function to sequentally apply function ruleA1.
    Used for the branch expressions in case expressions.
|-}
applyRuleA1ForBranches :: [DataType] -> ([FreeVar], [TypeComp]) -> [(ConName, [TypeComp])] -> [FreeVar] -> [Branch] -> [Branch] -> ([(ConName, [TypeComp])], [Branch])
applyRuleA1ForBranches gamma (phi, tcomps) ctcomps fvs [] bs' = (ctcomps, bs')
applyRuleA1ForBranches gamma (phi, tcomps) ctcomps fvs1 ((c, fvs2, dt) : bs) bs' = let (phi', tcomps') = getNonInductiveBindersTypes gamma c fvs2 -- phi' is non-inductives of binders fvs2. tcomps' are types of phi'. for this branch.
                                                                                       fvs1' = foldr (\fv fvs -> let fv' = rename fvs fv in fv':fvs) fvs1 fvs2 -- add new free variables for fvs2 at head of fvs1
                                                                                       fvs2' = take (length fvs2) fvs1' -- take the new free variables created for fvs2
                                                                                       (ctcomps', dt') = ruleA1 gamma (phi ++ phi', tcomps ++ tcomps') ctcomps fvs1' (foldr (\fv dt -> subst (DFreeVarApp fv []) dt) dt fvs2') -- substitute fvs2' in dt and transform
                                                                                       dt'' = foldl (\dt fv -> abstract fv dt) dt' fvs2'
                                                                                   in applyRuleA1ForBranches gamma (phi, tcomps) ctcomps' fvs1 bs (bs' ++ [(c, fvs2, dt'')])


{-|
    Function to sequentially apply function ruleA2.
    Used for the arguments of variable and constructor applications.
|-}
applyRuleA2ForArguments :: [DataType] -> [(ConName, [TypeComp])] -> [FreeVar] -> DTerm -> [DTerm] -> ([(ConName, [TypeComp])], DTerm)
applyRuleA2ForArguments gamma ctcomps fvs ft [] = (ctcomps, ft)
applyRuleA2ForArguments gamma ctcomps fvs ft (dt:dts) = let (ctcomps', dt') = ruleA2 gamma ctcomps fvs dt
                                                        in applyRuleA2ForArguments gamma ctcomps' fvs (DFunApp "(++)" [ft, dt']) dts


{-|
    Function to create a new constructor name for the flat data type.
|-}
newFlatConName :: [ConName] -> ConName
newFlatConName [] = "flatCon"
newFlatConName cs = newFlatConName' cs (head cs)
newFlatConName' cs c = if (c `elem` cs)
                       then newFlatConName' cs (c ++ "'")
                       else c


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
rename fvs fv = if (fv `elem` fvs)
                then rename fvs (fv ++ "'")
                else fv


{-|
    TBD: Function to substitute dt0 in dt1.
|-}
subst :: DTerm -> DTerm -> DTerm
subst dt0 dt1 = subst' 0 dt0 dt1

subst' :: Int -> DTerm -> DTerm -> DTerm
subst' i dt0 (DFreeVarApp fv dts) = DFreeVarApp fv (map (subst' i dt0) dts)
subst' i dt0 (DBoundVarApp j dts) = if (j < i)
                                    then DBoundVarApp j (map (subst' i dt0) dts)
                                    else if (j == i)
                                         then shift i 0 dt0 -- TBD: what is the DTerm to be constructed here ??
                                         else DBoundVarApp (j-1) (map (subst' (i-1) dt0) dts) -- TBD: (i-1) or (j-1) ??
subst' i dt0 (DConApp c dts) = DConApp c (map (subst' i dt0) dts)
subst' i dt0 (DLambda fv dt) = DLambda fv (subst' (i+1) dt0 dt)
subst' i dt0 (DFunApp f dts) = DFunApp f (map (subst' i dt0) dts)
subst' i dt0 (DLet fv dt1 dt2) = DLet fv (subst' i dt0 dt1) (subst' (i+1) dt0 dt2)
subst' i dt0 (DCase (fv, dts) bs) = let (DFreeVarApp fv' dts') = subst' i dt0 (DFreeVarApp fv dts)
                                        bs' = map (\(c, fvs, dt) -> (c, fvs, subst' (i+(length fvs)) dt0 dt)) bs
                                    in (DCase (fv', dts') bs')
subst' i dt0 (DWhere f1 dts (f2, fvs, dt)) = let (DFunApp f1' dts') = subst' i dt0 (DFunApp f1 dts)
                                             in (DWhere f1' dts' (f2, fvs, subst' (i+(length fvs)) dt0 dt)) -- TBD: verify (d+(length fvs))


{-|
    TBD: Function to shift De Bruijn index for substitution.
|-}
shift :: Int -> Int -> DTerm -> DTerm
shift 0 d dt = dt
shift i d (DFreeVarApp fv dts) = DFreeVarApp fv (map (shift i d) dts)
shift i d (DBoundVarApp j dts) = if (j >= d)
                                 then DBoundVarApp (j+i) (map (shift i (d+1)) dts) -- TBD: verify (d+1)
                                 else DBoundVarApp j (map (shift i (d+1)) dts) -- TBD: verify (d+1)
shift i d (DConApp c dts) = DConApp c (map (shift i d) dts)
shift i d (DLambda fv dt) = DLambda fv (shift i (d+1) dt)
shift i d (DFunApp f dts) = DFunApp f (map (shift i d) dts)
shift i d (DLet fv dt0 dt1) = DLet fv (shift i d dt0) (shift i (d+1) dt1)
shift i d (DCase (fv, dts) bs) = let (DFreeVarApp fv' dts') = shift i d (DFreeVarApp fv dts)
                                     bs' = map (\(c, fvs, dt) -> (c, fvs, shift i (d+length fvs) dt)) bs
                                 in (DCase (fv', dts') bs')
shift i d (DWhere f1 dts (f2, fvs, dt)) = let (DFunApp f1' dts') = shift i d (DFunApp f1 dts)
                                          in (DWhere f1' dts' (f2, fvs, shift i (d+(length fvs)) dt)) -- TBD: verify (d +(length fvs))


{-|
    TBD: Function to abstract the free variable fv in dt with its De Bruijn index.
|-}
abstract :: FreeVar -> DTerm -> DTerm
abstract fv dt = abstract' 0 fv dt

abstract' :: Int -> FreeVar -> DTerm -> DTerm
abstract' i fv dt@(DFreeVarApp fv1 dts) = dt
abstract' i fv dt@(DBoundVarApp j dts) = dt
abstract' i fv dt@(DConApp c dts) = dt
abstract' i fv dt@(DLambda fv1 dt1) = dt
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
    Returns ([non-inductive binder], [their type component])

-- getTypeComponents for c can never be [], because fvs for c is not [].
-- => filter in getTypeComponents is never []. => head is never applied on [].
|-}
getNonInductiveBindersTypes :: [DataType] -> ConName -> [FreeVar] -> ([FreeVar], [TypeComp])
getNonInductiveBindersTypes gamma c [] = ([], [])
getNonInductiveBindersTypes gamma c fvs = let tcomps = concatMap (getTypeComponents c) gamma
                                              pairs = zip fvs tcomps
                                          in unzip (filter (\(fv, tcomp) -> tcomp `notElem` gamma) pairs)

getTypeComponents :: ConName -> DataType -> [TypeComp]
getTypeComponents c (DataType tname tvars tcontcomps) = (snd . head) (filter (\(tcon, tcomps) -> tcon == c) tcontcomps)
