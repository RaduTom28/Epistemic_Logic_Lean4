import EpistemicLogicLean4.Definitions

set_option autoImplicit false


structure kripkeModel where
  world : Type
  relation : Nat → world → world → Prop
  valuation : world → Char → Prop

@[simp]
def isSatisfied (M : kripkeModel) (w : M.world) (φ : formula) :=
  match φ with
  | ⊥ => False
  | formula.atomic_prop p => M.valuation w p
  | ~ ψ => ¬ isSatisfied M w ψ
  | χ ↣ ψ => isSatisfied M w χ → isSatisfied M w ψ
  | formula.box i ψ => ∀ (v : M.world), (M.relation i w v → isSatisfied M v ψ)


variable {φ ψ : formula} {M : kripkeModel} {w: M.world}
variable {p q : Prop}
variable {i: Nat}
variable {r: Char}


open Classical

@[simp]
theorem aux0 : ¬¬q ↔ q := by
  apply Iff.intro
  case mpr =>
    intros hq hnq
    contradiction
  case mp =>
  intros hnnq
  apply Or.elim (em q)
  case left =>
    intros hq
    assumption
  case right =>
    intros hnq
    contradiction
  done

@[simp]
theorem aux1 : p ∧ ¬q ↔ ¬ (p → q) := by
  apply Iff.intro
  case mpr =>
    intro h
    apply Or.elim (em p)
    case left =>
      intro hp
      apply Or.elim (em q)
      case left =>
        intro hq
        have hpq := And.intro hp hq
        constructor
        case left =>
          assumption
        case right =>
        have aux : (p ∧ q) → (p → q) := by
          intros hpq hq
          exact And.right hpq
        have contra := aux hpq
        contradiction
      case right=>
        intro hnq
        exact And.intro hp hnq
    case right =>
      intro hnp
      apply Or.elim (em q)
      case left =>
        intro hq
        constructor
        case left =>
          have aux : ¬p ∧ q → p → q := by
            intros h hp
            have hnp := And.left h
            contradiction
          have hptoq := aux (And.intro hnp hq)
          contradiction
        case right =>
          intros duplicate
          have aux : ¬p ∧ q → p → q := by
              intros h hp
              have hnp := And.left h
              contradiction
          have hptoq := aux (And.intro hnp hq)
          contradiction
      case right =>
        intros hnq
        have aux : ¬p ∧ ¬q → p → q := by
          intros hnpnq hp
          have hnq := And.left hnpnq
          contradiction
        have hptoq := aux (And.intro hnp hnq)
        contradiction
  case mp =>
    intros hphnq hptoq
    have hq := hptoq (And.left hphnq)
    have hnq := And.right hphnq
    contradiction
  done


@[simp]
theorem aux2: ¬(p → ¬q) ↔ (p ∧ q) := by
  rw[←aux1, aux0]
  simp
  done

@[simp]
theorem prop_sat : isSatisfied M w (prop r) ↔ M.valuation w r := by simp

@[simp]
theorem not_sat : isSatisfied M w (~ φ) ↔  ¬ isSatisfied M w φ := by simp

@[simp]
theorem if_sat : isSatisfied M w (φ ↣ ψ) ↔ isSatisfied M w φ → isSatisfied M w ψ := by simp

@[simp]
theorem k_sat : isSatisfied M w ((K i) φ ) ↔ ∀ (v: M.world),  (M.relation i w v → isSatisfied M v φ) := by simp

@[simp]
theorem and_sat : isSatisfied M w (φ ⋏ ψ) ↔ (isSatisfied M w φ ) ∧ (isSatisfied M w ψ) := by simp
