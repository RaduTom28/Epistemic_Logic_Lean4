import EpistemicLogicLean4.Definitions
set_option autoImplicit false


def axiom_T {φ : formula } {i : Nat} := (K i) φ ↣ φ
def axiom_D' {φ : formula} {i : Nat} := ~ (K i) (φ ⋏ ~ φ)
def axiom_B {φ : formula} {i : Nat} := φ ↣ (K i) (~(K i) (~ φ))
def axiom_4 {φ : formula} {i : Nat} := (K i) φ ↣ (K i) ((K i) φ)
def axiom_5' {φ : formula} {i : Nat} := ~ (K i) φ ↣ (K i) (~ (K i) φ)


set_option hygiene false in prefix:100 "⊢S5" => S5Provable
inductive S5Provable : formula → Prop where
| modusPonens {φ ψ : formula} : ⊢S5 φ → ⊢S5 (φ ↣ ψ) → ⊢S5 ψ
| K_axiom {φ ψ : formula} {i : Nat} : ⊢S5 ((K i) (φ ↣ ψ) ↣ ((K i) φ ↣ (K i) ψ))
| necessitation {φ : formula} {i : Nat}: ⊢S5 φ → ⊢S5 (K i) φ
| axiom_T {φ : formula } {i : Nat} : ⊢S5 ((K i) φ ↣ φ)
| axiom_D' {φ : formula} {i : Nat} : ⊢S5 ((K i) (φ ⋏ ~ φ))
| axiom_B {φ : formula} {i : Nat} : ⊢S5 (φ ↣ (K i) (~(K i) (~ φ)))
| axiom_4 {φ : formula} {i : Nat} : ⊢S5 ((K i) φ ↣ (K i) ((K i) φ))
| axiom_5' {φ : formula} {i : Nat} : ⊢S5 (~ (K i) φ ↣ (K i) (~ (K i) φ))


--S5Provable only to be used when we assume common knowledge for the hypothesis
-- referenced "S. Artemov / Towards Syntactic Epistemic Logic"
