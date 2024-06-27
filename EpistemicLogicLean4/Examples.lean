import EpistemicLogicLean4.Definitions
import EpistemicLogicLean4.Semantics
set_option autoImplicit false

variable {φ ψ : formula} {M : kripkeModel} {w: M.world}
variable {p q : Prop}
variable {i: Nat}
variable {r: Char}

inductive ExampleWorld : Type
| s : ExampleWorld
| t : ExampleWorld
| u : ExampleWorld

open ExampleWorld

def model1 : kripkeModel :=
{
  world := ExampleWorld
  relation := ( λ i w v =>
  ((i = 1) ∧ (((w = s) ∨ (w = t)) ∧ ((v = s) ∨ (v = t))) ∨ ((w = u) ∧ (v = u)))
  ∨
  ((i = 2) ∧ (((w = s) ∨ (w = u)) ∧ ((v = s) ∨ (v = u))) ∨ ((w = t) ∧ (v = t))) )

  valuation := (λ w c =>
  ((w = s) ∨ (w = u)) ∧ (c = 'p')
  )
}

@[simp]
theorem aux_exemplu1 : 2 = 1 ∧ p ∧ q → False := by simp

@[simp]
theorem aux_exemplu2 : s = u ∧ t = u → False := by simp

@[simp]
theorem aux_exemplu3: p ∧ q ∧ (t = s ∨ t = u) → False := by simp

@[simp]
theorem aux_exemplu4: s = t ∧ t = t → False := by simp

theorem aux_exemplu: kripkeModel.relation model1 2 s t → False := by
  intros h
  cases h with
  | inl hl =>
    cases hl with
    | inl hll =>
      have lll := aux_exemplu1 hll
      assumption
    | inr hlr =>
      have llr := aux_exemplu2 hlr
      assumption
  | inr hr =>
    cases hr with
    | inl hrl =>
      have lrl := aux_exemplu3 hrl
      assumption
    | inr hrr =>
      have lrr := aux_exemplu4 hrr
      assumption
  done


theorem exemplu: isSatisfied model1 s ((K 2) (prop 'p')) := by
  simp
  intros h h1
  constructor
  case right =>
    rfl
  case left =>
    cases h with
    |s =>
      constructor
      rfl
    |u =>
      simp
    |t =>
      have lt := aux_exemplu h1
      contradiction
  done
