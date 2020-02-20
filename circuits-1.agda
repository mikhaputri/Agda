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

buildCircuit : {n : ℕ} → (Vec Bool n → Bool) → Circuit n
buildCircuit f = ?


buildCircuitOk : {n : ℕ} → (f : Vec Bool n → Bool) →
                 (bs : Vec Bool n) → eval (buildCircuit f) bs ≡ f bs 
buildCircuitOk f bs = ?

