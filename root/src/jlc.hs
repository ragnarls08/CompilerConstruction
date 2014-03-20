import System.Environment (getArgs)
import System.Exit

import AbsJavalette
import LexJavalette
import ParJavalette
import PrintJavalette
import ErrM

import TypeChecker


check :: String -> IO () 
check s = case pProgram (myLexer s) of
	Bad err  -> do 
			putStrLn "SYNTAX ERROR"
			putStrLn err
			exitFailure 
	Ok  tree -> 
			case typecheck tree of
				Bad err -> do 
					putStrLn "TYPE ERROR"
					putStrLn err
					exitFailure 
				Ok tree' -> print $ printTree tree

main :: IO ()
main = do 
	args <- getArgs
	case args of
		[file] -> do 
			f <- readFile file 
			check f			
		_-> do 
			putStrLn "Usage: lab3 <SourceFile>"
			exitFailure

