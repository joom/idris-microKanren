module MicroKanren

%access public export

Var : Type
Var = Integer

data Term = Atom String | Pair Term Term | TVar Var
data KList a = KNil | KCons a (KList a) | KDelay (KList a)

Subst : Type
Subst = List (Var, Term)

State : Type
State = (Subst, Integer)

Program : Type
Program = State -> KList State

klistToList : KList a -> List a
klistToList KNil = []
klistToList (KCons x xs) = x :: klistToList xs
klistToList (KDelay xs) = klistToList xs

(<|>) : KList a -> KList a -> KList a
(<|>) KNil xs = xs
(<|>) (KCons x xs) ys = KCons x ((<|>) ys xs)
(<|>) (KDelay xs) ys = KDelay ((<|>) ys xs)

(>>=) : KList a -> (a -> KList b) -> KList b
(>>=) KNil f = KNil
(>>=) (KCons x xs) f = (f x) <|> ((>>=) xs f)
(>>=) (KDelay xs) f = KDelay ((>>=) xs f)

||| Apply a substitution to the top level of a term
walk : Term -> Subst -> Term
walk (TVar v) s =
  case lookup v s of
       Nothing => TVar v
       Just us => walk us s
walk u s = u

extS : Var -> Term -> Subst -> Subst
extS x v s = (x, v) :: s

||| Try to unify two terms under a substitution;
||| pure an extended subst if it succeeds
unify : Term -> Term -> Subst -> Maybe Subst
unify u v s = un (walk u s) (walk v s)
  where
    un : Term -> Term -> Maybe Subst
    un (TVar x1) (TVar x2) =
      Just $ if x1 == x2 then s else extS x1 (TVar x2) s
    un (TVar x1) v = Just $ extS x1 v s
    un u (TVar x2) = Just $ extS x2 u s
    un (Pair u1 u2) (Pair v1 v2) =
      unify u1 v1 s >>= unify u2 v2
    un (Atom a1) (Atom a2) =
      if a1 == a2 then Just s else Nothing
    un _ _  = Nothing

-- MicroKanren program formers
zzz : Program -> Program
zzz g = \sc => KDelay (g sc)

equiv : Term -> Term -> Program
equiv u v = \(s, c) => case unify u v s of
  Nothing => KNil
  Just s' => KCons (s', c) KNil

fresh : (Term -> Program) -> Program
fresh f = \(s, c) => f (TVar c) (s, c + 1)

disj : Program -> Program -> Program
disj g1 g2 = \sc => (g1 sc) <|> (g2 sc)

conj : Program -> Program -> Program
conj g1 g2 = \sc => g1 sc >>= g2

-- Running

emptyState : State
emptyState = ([], 0)

runTest : Program -> List (Subst, Integer)
runTest p = klistToList (p emptyState)
