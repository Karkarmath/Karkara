import Control.Applicative ( (<$), (<$>) )
import Data.Map as Map  
import Control.Monad ( guard )

-- Синоним для читабельности (String выбран для того, чтобы было больше возможных символов для абстрагирования).
type Symb = String

-- Инфиксные конструкторы для удобства.
infixl 4 :@
infixr 3 :->
 
-- Построение термов по Чёрчу.
data Expr = Var Symb 
            | Expr :@ Expr
            | Lam Symb Type Expr
    deriving (Eq,Show)
 
-- Построение типов.
data Type = TVar Symb 
            | Type :-> Type
    deriving (Eq,Show)

-- Упаковка контекста (синоним).
type Env = Map Symb Type

-- Удобства для будущих тестов.
(--->) :: Integer -> Integer -> Type 
a ---> b = TVar (show a) :-> TVar (show b)
infixr 3 --->

(@@) :: Symb -> Symb -> Expr
a @@ b = Var a :@ Var b
infixl 4 @@

-- Выведение типов (потом будем в check поданный тип сравнивать с выведенным).
eval :: Env -> Expr -> Maybe Type
eval env (Var v) = Map.lookup v env
eval env (Lam v ty tm) = (ty :->) <$> eval (Map.insert v ty env) tm
eval env (tm :@ tm') = do
    i :-> o <- eval env tm
    i' <- eval env tm'
    guard (i == i')
    return o

-- Собственно, сама проверка, ничего неожиданного.
check :: [(Symb,Type)] -> Expr -> Type -> Bool 
check xss tr ty = case eval (fromList xss) tr of
    Just t -> t == ty
    Nothing -> False