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


{-|
    Generates the definition for flatten and the new constructors for the Flat Data Type.
|-}
generateFlatten :: DTerm -> ([ConName], DTerm)
generateFlatten dt = ruleA1 [] [] dt


{-|
    Definition for transformation rule A1.
|-}
-- ruleA1 :: [Non-inductive Components] -> [New Flat Constructors] -> Flat Term -> ([New Flat Constructors], Flat Term)
ruleA1 :: [FreeVar] -> [ConName] -> DTerm -> ([ConName], DTerm)
ruleA1 phi cs (DFreeVarApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                     in applyRuleA2ForArguments cs' (DConApp (head cs') (toDFreeVarApps phi)) dts

-- ruleA1 phi cs (DFreeVarApp fv dts) = let f = \(cs, ft) dt -> let (cs', dt') = ruleA2 cs dt
--                                                              in (cs', (DFunApp "(++)" [ft, dt']))
--                                          cs' = addFlatConName cs
--                                          newFlatConApp  = DConApp (head cs') (toDFreeVarApps phi)
--                                      in foldl f (cs', newFlatConApp) dts

ruleA1 phi cs (DBoundVarApp i dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                     in applyRuleA2ForArguments cs' (DConApp (head cs') (toDFreeVarApps phi)) dts

-- ruleA1 phi cs (DBoundVarApp i dts) = let f = \(cs, ft) dt -> let (cs', dt') = ruleA2 cs dt
--                                                              in (cs', (DFunApp "(++)" [ft, dt']))
--                                          cs' = addFlatConName cs
--                                          newFlatConApp  = DConApp (head cs') (toDFreeVarApps phi)
--                                      in foldl f (cs', newFlatConApp) dts

ruleA1 phi cs (DConApp fv dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                 in applyRuleA2ForArguments cs' (DConApp (head cs') (toDFreeVarApps phi)) dts

-- ruleA1 phi cs (DConApp fv dts) = let f = \(cs, ft) dt -> let (cs', dt') = ruleA2 cs dt
--                                                              in (cs', (DFunApp "(++)" [ft, dt']))
--                                          cs' = addFlatConName cs
--                                          newFlatConApp  = DConApp (head cs') (toDFreeVarApps phi)
--                                      in foldl f (cs', newFlatConApp) dts

ruleA1 phi cs (DLambda fv dt) = ruleA1 phi cs dt

ruleA1 phi cs (DFunApp f dts) = let cs' = addFlatConName cs -- create a new constructor for flat data type at head of cs'
                                in (cs', DFunApp "(++)" [(DConApp (head cs') (toDFreeVarApps phi)) , (DFunApp ("flatten_" ++ f) (concatMap free dts))])

ruleA1 phi cs (DLet fv dt0 dt1) = ruleA1 phi cs (subst dt0 dt1)

ruleA1 phi cs (DCase csel bs) = let (cs', bs') = applyRuleA1ForBranch phi cs bs []
                                in (cs', (DCase csel bs'))

ruleA1 phi cs (DWhere f1 dts (f2, fvs, dt)) = let (cs', dt') = ruleA1 [] cs dt
                                              in (cs', (DWhere ("flatten_" ++ f1) dts (("flatten_" ++ f2), fvs, dt')))


{-|
    Definition for transformation rule A2.
|-}
ruleA2 :: [ConName] -> DTerm -> ([ConName], DTerm)
ruleA2 cs (DFreeVarApp fv dts) = applyRuleA2ForArguments cs (DConApp "[]" []) dts
ruleA2 cs (DBoundVarApp i dts) = applyRuleA2ForArguments cs (DConApp "[]" []) dts
ruleA2 cs (DConApp c dts) = applyRuleA2ForArguments cs (DConApp "[]" []) dts
ruleA2 cs (DLambda fv dt) = ruleA2 cs dt
ruleA2 cs (DFunApp f dts) = (cs, (DFunApp ("flatten_" ++ f) (concatMap free dts)))
ruleA2 cs (DLet fv dt0 dt1) = ruleA2 cs (subst dt0 dt1)
ruleA2 cs dt = ruleA1 [] cs dt


{-|
    Function to sequentally apply function ruleA1.
    Used for the branch expressions in case expressions.
|-}
applyRuleA1ForBranch :: [FreeVar] -> [ConName] -> [Branch] -> [Branch] -> ([ConName], [Branch])
applyRuleA1ForBranch phi cs [] bs' = (cs, bs')
applyRuleA1ForBranch phi cs ((c, fvs, dt) : bs) bs' = let phi' = phi
                                                          (cs', dt') = ruleA1 phi' cs dt
                                                      in applyRuleA1ForBranch phi cs' bs (bs' ++ [(c, fvs, dt')])


{-|
    Function to sequentially apply function ruleA2.
    Used for the arguments of variable and constructor applications.
|-}
applyRuleA2ForArguments :: [ConName] -> DTerm -> [DTerm] -> ([ConName], DTerm)
applyRuleA2ForArguments cs ft [] = (cs, ft)
applyRuleA2ForArguments cs ft (dt:dts) = let (cs', dt') = ruleA2 cs dt
                                         in applyRuleA2ForArguments cs' (DFunApp "(++)" [ft, dt']) dts


{-|
    Function to add a new constructor for the flat data type.
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
toDFreeVarApps vs = map (\v -> (DFreeVarApp v [])) vs


subst dt0 dt1 = dt1
free = \dt -> []
