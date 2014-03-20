module TypeChecker where

import AbsJavalette
import PrintJavalette
import ErrM
import Data.Map(Map, insert, empty, fromList, lookup)
import Data.Maybe(fromJust)
import Control.Monad(foldM)


-- | functions and context stack
--type Env = (Sig,[Context]) 
---- | function type signature
--type Sig = Map Id ([Type],Type) 
---- | variables with their types
--type Context = Map Id Type 


-- | Typecheck a full program
typecheck :: Program -> Err Program
typecheck (Program tdefs) = error $ show tdefs

