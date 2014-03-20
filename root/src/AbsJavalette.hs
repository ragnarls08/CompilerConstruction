module AbsJavalette where

-- Haskell module generated by the BNF converter


newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Program [TopDef]
  deriving (Eq,Ord,Show)

data TopDef =
   FnDef Type Ident [Arg] Block
  deriving (Eq,Ord,Show)

data Arg =
   Arg Type Ident
  deriving (Eq,Ord,Show)

data Block =
   Block [Stmt]
  deriving (Eq,Ord,Show)

data Stmt =
   Empty
 | BStmt Block
 | Decl Type [Item]
 | Ass Ident Expr
 | Incr Ident
 | Decr Ident
 | Ret Expr
 | VRet
 | Cond Expr Stmt
 | CondElse Expr Stmt Stmt
 | While Expr Stmt
 | SExp Expr
  deriving (Eq,Ord,Show)

data Item =
   NoInit Ident
 | Init Ident Expr
  deriving (Eq,Ord,Show)

data Type =
   Int
 | Doub
 | Bool
 | Void
 | Fun Type [Type]
  deriving (Eq,Ord,Show)

data Expr =
   EVar Ident
 | ELitInt Integer
 | ELitDoub Double
 | ELitTrue
 | ELitFalse
 | EApp Ident [Expr]
 | EString String
 | Neg Expr
 | Not Expr
 | EMul Expr MulOp Expr
 | EAdd Expr AddOp Expr
 | ERel Expr RelOp Expr
 | EAnd Expr Expr
 | EOr Expr Expr
  deriving (Eq,Ord,Show)

data AddOp =
   Plus
 | Minus
  deriving (Eq,Ord,Show)

data MulOp =
   Times
 | Div
 | Mod
  deriving (Eq,Ord,Show)

data RelOp =
   LTH
 | LE
 | GTH
 | GE
 | EQU
 | NE
  deriving (Eq,Ord,Show)

