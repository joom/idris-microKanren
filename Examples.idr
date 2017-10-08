module Examples

import MicroKanren

five : Program
five = fresh (\x => equiv x (Atom "5"))

fives_ : Term -> Program
fives_ x = disj (equiv x (Atom "5")) (zzz $ fives_ x)

fives : Program
fives = fresh fives_

fivesRev_ : Term -> Program
fivesRev_ x = disj (zzz $ fivesRev_ x) (equiv x (Atom "5"))

fivesRev : Program
fivesRev = fresh fivesRev_

a_and_b : Program
a_and_b = conj
          (fresh (\a => equiv a (Atom "7")))
          (fresh (\b => disj (equiv b (Atom "5")) (equiv b (Atom "6"))))

elemo : Term -> Term -> Program
elemo e l = fresh $ \x => fresh $ \xs =>
    (equiv (Pair e xs) l)
    `disj`
    ((equiv (Pair x xs) l) `conj` (zzz $ elemo e xs))

appendo : Term -> Term -> Term -> Program
appendo l s out =
  disj (conj (equiv (Atom "nil") l) (equiv s out)) $
        fresh $ \a => fresh $ \d => fresh $ \res =>
          conj (equiv (Pair a d) l) $
                  conj (equiv (Pair a res) out)
                      (zzz $ appendo d s res)

-- Bunch of terms to test with
a : Term
b : Term
c : Term
d : Term
e : Term
xs : Term
ys : Term
xsys : Term
nil : Term
a = Atom "a"
b = Atom "b"
c = Atom "c"
d = Atom "d"
e = Atom "e"
nil = Atom "nil"
xs = foldr Pair nil [a,b,c]
ys = foldr Pair nil [d,e]
xsys = foldr Pair nil [a,b,c,d,e]
