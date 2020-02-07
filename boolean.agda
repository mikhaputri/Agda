open import Data.Bool
open import Relation.Binary.PropositionalEquality

neg : Bool → Bool
neg false = true
neg true = false

nand : Bool → Bool → Bool
nand false y = true
nand true false = true
nand true true = false

or : Bool →  Bool → Bool
or false c = c
or true c = true

orx : Bool → Bool → Bool
orx b c = nand (nand b b) (nand c c)

lemma : (x y : Bool) → or x y ≡ orx x y
lemma false false  = refl
lemma false true = refl
lemma true false = refl
lemma true true = refl

lemma' : (x y : Bool) → or x y ≡ orx x y
lemma' false false = refl
lemma' false true = refl
lemma' true y = refl

f0 : Bool → Bool → Bool
f0 x y = true

g0 : Bool → Bool
g0 x = false

g1 : Bool → Bool
g1 x = true

g2 : Bool → Bool
g2 x = x

g3 : Bool -> Bool
g3 x = neg x

eqb : Bool → Bool → Bool
eqb false false = true
eqb false true = false
eqb true false = false
eqb true true = true

eqbx : Bool → Bool → Bool
eqbx x y = nand (nand x y) (nand (nand x x) (nand y y))

eqb-lem : (x y : Bool) → eqb x y ≡ eqbx x y
eqb-lem false false = refl
eqb-lem false true = refl
eqb-lem true false = refl
eqb-lem true true = refl

and : Bool → Bool → Bool
and false false = false
and false true = false
and true false = false
and true true = true

xor : Bool → Bool → Bool
xor false x = x
xor true false = true
xor true true = false

imp : Bool → Bool → Bool
imp false x = true
imp true false = false
imp true true = true

h0 : Bool → Bool → Bool
h0 x y = true

h1 : Bool → Bool → Bool
h1 x y = false

h2 : Bool → Bool → Bool
h2 x y = x

h3 : Bool → Bool → Bool
h3 x y = neg x

h4 : Bool → Bool → Bool
h4 x y = y

h5 : Bool → Bool → Bool
h5 x y = neg y

h6 : Bool → Bool → Bool
h6 x y = and x y

h7 : Bool → Bool → Bool
h7 x y = nand x y

h8 : Bool → Bool → Bool
h8 x y = and x (neg y)

h9 : Bool → Bool → Bool
h9 x y = and (neg x) y

h10 : Bool → Bool → Bool
h10 x y = or x y

h11 : Bool → Bool → Bool
h11 x y = eqb x y

h12 : Bool → Bool → Bool
h12 x y = neg (or x y)

h13 : Bool → Bool → Bool
h13 x y = xor x y

h14 : Bool → Bool → Bool
h14 x y = imp x y

h15 : Bool → Bool → Bool
h15 x y = imp y x 
