open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Circuit : ℕ → Set where
  const : {n : ℕ} → Bool → Circuit n
  input : {n : ℕ} → Fin n → Circuit n
  nand : {n : ℕ} → Circuit n → Circuit n → Circuit n

notc : Circuit 1
notc = nand (input zero) (input zero)

andc : Circuit 2
andc = nand (nand (input zero) (input (suc zero)))
            (nand (input zero) (input (suc zero)))

orc : Circuit 2
orc = nand (nand (input zero) (input zero))
           (nand (input (suc zero)) (input (suc zero)))

_!!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
(x ∷ xs) !! zero = x
(x ∷ xs) !! suc i = xs !! i

nandf : Bool → Bool → Bool
nandf false c = true
nandf true false = true
nandf true true = false

eval : {n : ℕ} → Circuit n → Vec Bool n → Bool
eval (const x) bs = x
eval (input x) bs = bs !! x
eval (nand p q) bs = nandf (eval p bs) (eval q bs)

x1 = eval notc (false ∷ [])
x2 = eval andc (true ∷ (true ∷ []))
x3 = eval orc (false ∷ (false ∷ []))

orf : Vec Bool 2 → Bool
orf (x ∷ y ∷ []) = x ∨ y

open import Data.List

l1 : List ℕ
l1 = 1 ∷ 2 ∷ 3 ∷ []
l2 : List ℕ
l2 = Data.List.map suc l1

allInputs : (n : ℕ) → List (Vec Bool n)
allInputs zero = Data.List.[_] [] 
allInputs (suc n) = let xs : List (Vec Bool n)
                        xs = allInputs n
                        fxs : List (Vec Bool (suc n))
                        fxs = Data.List.map (λ x → false ∷ x) xs
                        txs : List (Vec Bool (suc n))
                        txs = Data.List.map (λ x → true ∷ x) xs
                     in fxs Data.List.++ txs

-- allinputs 2 = ..

eqb : Bool → Bool → Bool
eqb false false = true
eqb false true = false
eqb true false = false
eqb true true = true

tester : {n : ℕ} → Circuit n → (Vec Bool n → Bool) → Bool
tester {n} c f = aux (allInputs n)   
  where aux : List (Vec Bool n) → Bool
        aux [] = true
        aux (x ∷ xs) = eqb (eval c x) (f x) ∧ aux xs  

test = tester orc orf
test2 = tester andc orf

-- look from allinput & tester, find lines that produce true
-- e.g x0 x1 x2 -> true false true -> true
-- then create the function -> x0 & !x1 & x2
-- combine all functions that made out of each lines into a circuit with OR
-- e.g x0 & !x1 & x2 , x0 & x1 & x2 , etc.

buildCircuit : {n : ℕ} → (Vec Bool n → Bool) → Circuit n
buildCircuit f = {!!}

buildCircuitOk : {n : ℕ} → (f : Vec Bool n → Bool) →
                 (bs : Vec Bool n) → eval (buildCircuit f) bs ≡ f bs 
buildCircuitOk f bs = {!!}

