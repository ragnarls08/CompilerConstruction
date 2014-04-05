module TypeChecker where

import AbsJavalette
import PrintJavalette
import ErrM
import Data.Map(Map, insert, empty, fromList, lookup)
import Data.Maybe(fromJust)
import Control.Monad(foldM)


-- | functions and context stack
type Env = (Sigs,[Context]) 
-- | function type signature
type Sigs = Map Ident ([Type],Type) 
-- | variables with their types
type Context = Map Ident Type 

-- | Typecheck a full program
typecheck :: Program -> Err Program
typecheck (Program tdefs) = do 
		(tdefs', _) <- checkTDefs newEnv tdefs 
		return (Program tdefs')
	where
		(s, con)   =  (makeEnv emptyEnv tdefs)
		(s1, con1) = (insert (Ident "printInt") 	([Int], 	Void)    s, con)
		(s2, con2) = (insert (Ident "printString") 	([String],	Void)   s1, con1)
		(s3, con3) = (insert (Ident "printDouble") ([Double],	Void)   s2, con2)
		(s4, con4) = (insert (Ident "readInt")	 	([],	 	Int)    s3, con3)
		newEnv     = (insert (Ident "readDouble") 	([],		Double) s4, con4)

-- | Checks program definitions
checkTDefs :: Env -> [TopDef] -> Err ([TopDef],Env)
checkTDefs env [] = return ([], env)
checkTDefs env (t:ts) = do
	(t' ,env') <- checkTDef env t
	(ts', env'') <- checkTDefs (popBlock env') ts 
	return (t':ts', env'')

checkTDef :: Env -> TopDef -> Err (TopDef,Env)
checkTDef env (FnDef typ id args (Block block)) = do
	env'  <- addArgs (newBlock env) args	
	(block', env'') <- checkStms env' typ block 
	return (FnDef typ id args (Block block'), env'')


checkStms :: Env -> Type -> [Stmt] -> Err ([Stmt], Env)
checkStms env typ []		= return ([], env)
checkStms env typ (s:ss)	= do	
	(s', env') <- checkStm env typ s
	(ss', env'') <- checkStms env' typ ss
	return (s':ss', env'')

checkStm :: Env -> Type -> Stmt -> Err (Stmt, Env)
checkStm env t s = 
	case s of
		Empty -> return (Empty, env)
		Ass id e -> do
			t' <- lookupVar env id 
			checkExp env e t'
			return (Ass id e, env)
		Incr id -> do
			typ <- lookupVar env id
			typeIn typ [Int, Double]
			return (Incr id, env)
		Decr id -> do
			typ <- lookupVar env id
			typeIn typ [Int, Double]
			return (Decr id, env)
		Ret exp -> do
			checkExp env exp t
			return (Ret exp, env)
		VRet -> if t == Void then return (VRet, env)
				else fail ("function returns type void but " ++ (show t) ++ " expected.")
		Decl typ is -> do
			e' <- checkItems env typ is
			return (Decl typ is, e')
		While e s -> do
			e' <- checkExp env e Bool
			(_, env') <- checkStm (newBlock env) t s
			return (While e' s, (popBlock env'))
		BStmt (Block block) -> do
			(block', env') <- checkStms (newBlock env) t block
			return (BStmt (Block block'), (popBlock env'))
		Cond e s -> do 
			e' <- checkExp env e Bool
			(_, env') <- checkStm env t s
			return (Cond e s, env')
		CondElse e s1 s2 -> do
			e' <- checkExp env e Bool			
			([s1',s2'], env') <- checkStms (newBlock env) t [s1,s2]
			return (CondElse e' s1' s2', (popBlock env'))
		SExp e -> do
			(e',t) <- inferExp env e
			return (SExp e', env)

typeIn :: Type -> [Type] -> Err Bool
typeIn t ts = if elem t ts then return True
				else fail ("expression has type " ++ printTree t
                    ++ " expected " ++ printTree ts)

-- | Checks items in an initialization list
checkItems :: Env -> Type -> [Item] -> Err Env
checkItems e t [] 	  = return e 
checkItems e t (i:is) = do
	case i of
		NoInit id -> do
			e' <- updateVar e t id
			checkItems e' t is
		Init id exp -> do
			checkExp e exp t
			e' <- updateVar e t id
			checkItems e' t is
	

checkExp :: Env -> Exp -> Type -> Err Exp
checkExp env e t = 
    do (e',t') <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return e'

inferExp :: Env -> Exp -> Err (Exp, Type)
inferExp env exp = do
	case exp of
		EVar id 	-> do 
			var <- lookupVar env id
			return (EVar id, var)
		EInt n 		-> return (EInt n, Int)		
		EDoub d 	-> return (EDoub d, Double)
		ETrue		-> return (ETrue, Bool)
		EFalse 		-> return (EFalse, Bool)
		EApp id exps  -> do 
			(tps, typ)  <- lookupFun env id
			exps' 		<- mapM (inferExp env) exps
			exps'		<- return $ map snd exps'
			zippid 		<- return $ zip tps exps'
			mapped 		<- return $ and $ map (\(x,y) -> x==y) zippid
			len 		<- return $ length tps == length exps'
			if len
				then 
					if mapped 
						then return (EApp id exps, typ)
						else fail $ "Type mismatch in argumentlist of " ++ printTree id
				else fail $ "Incorrect number of agruments in call to function " ++ printTree id
		EString s -> do return (EString s, String)
		Neg e -> do
			typ <- inferBin	[Int, Double] env e e
			return (Neg e, typ)
		Not e -> do
			typ <- inferBin [Bool] env e e
			return (Not e, typ)
		EMul l op r	-> do 
			typ <- inferMul [Int, Double] env l op r
			return (EMul l op r, typ)
		EAdd l op r	-> do 
			typ <- inferAdd [Int, Double] env l op r
			return (EAdd l op r, typ)
		ERel l op r	-> do 
			typ <- inferRel [Int, Double, Bool] env l op r
			return (ERel l op r, typ)			

		EAnd l r 	-> do
			typ <- inferBin [Bool] env l r
			return (EAnd l r, typ)
		EOr  l r 	-> do
			typ <- inferBin [Bool] env l r
			return (EOr l r, typ)

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types e l r = do
	(_, typ) <- inferExp e l
	if elem typ types
		then do 
			checkExp e r typ
			return typ
		else
			fail $ "wrong type of expression " ++ printTree l


-- | Always returns a bool, checks if l and r has same types
inferRel :: [Type] -> Env -> Exp -> RelOp -> Exp -> Err Type
inferRel types e l op r = do
		inferBin types e l r
		return Bool

inferAdd :: [Type] -> Env -> Exp -> AddOp -> Exp -> Err Type
inferAdd types e l op r = inferBin types e l r

inferMul :: [Type] -> Env -> Exp -> MulOp -> Exp -> Err Type
inferMul types e l op r = inferBin types e l r

-- | adds the arguements to the current context
addArgs :: Env -> [Arg] -> Err Env
addArgs env args = case args of 
	[] -> return env
	(Arg typ id) : rest -> do
		env' <- updateVars env typ [id]
		addArgs env' rest

-- | Initializes an environment with all function definitions
makeEnv :: Env -> [TopDef] -> Env
makeEnv e [] = e
makeEnv (sig, cont) ((FnDef typ id args _):dfs) = 
		makeEnv (sig', cont) dfs
	where
		sig'  = insert id (args',typ) sig 
		args' = inferArgs args

-- | 
inferArgs :: [Arg] -> [Type]
inferArgs [] = [] 
inferArgs ((Arg typ _):as) = typ : (inferArgs as)



-- | Crates an empty environment with a fresh block
emptyEnv :: Env
emptyEnv = newBlock (empty, [])		

-- | Creates a new context block
newBlock :: Env -> Env
newBlock (s, con) = (s, empty : con)

-- | Sets the environment up by one scope (context)
popBlock :: Env -> Env
popBlock (s,   []) = (s, [])
popBlock (s, c:cs) = (s, cs)


--------------------
-- Helper functions
--------------------
lookupFun :: Env -> Ident -> Err ([Type],Type)
lookupFun (sig, _) id = do	
	case (Data.Map.lookup id sig) of
		Nothing  -> fail $ "Function " ++ printTree id ++ " does not exist"
		Just ret -> return $ ret

lookupVar :: Env -> Ident -> Err Type
lookupVar (s, c) id = 
	if null l 
		then fail $ "Variable " ++ printTree id ++ " does not exist in the current scope" 
		else return $ fromJust $ head l
	where l = Prelude.filter (/=Nothing) $ Prelude.map (Data.Map.lookup id) c 

lookupVarScope :: Env -> Ident -> Err Type
lookupVarScope (s, c) id = do 
	case Data.Map.lookup id (head c) of
		Just v  -> return v
		Nothing -> fail $ "Variable " ++ printTree id ++ " does not exist in the current scope" 
	 

-- | Extend the environment with multiple new variables
updateVars :: Env -> Type -> [Ident] -> Err Env
updateVars env typ ids = case ids of
		[] -> return env
		x : rest -> do
		env' <- updateVar env typ x
		updateVars env' typ rest

-- | Extend the environment with new variables
updateVar :: Env -> Type -> Ident -> Err Env
updateVar (s, []) _ _ = fail "something went terribly wrong"
updateVar (s, c:cs) typ id = 
	case lookupVarScope (s, c:cs) id of
		Bad x -> return (s, (insert id typ c) : cs)
		Ok  x -> fail $ "Variable " ++ printTree id ++ " already defined in scope"