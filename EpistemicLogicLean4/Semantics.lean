import EpistemicLogicLean4.Definitions

set_option autoImplicit false


structure kripkeModel where
  world : Type
  relation : Nat → world → world → Prop
  valuation : world → Char → Prop


def isSatisfied (M : kripkeModel) (w : M.world) (φ : formula) :=
  match φ with
  | ⊥ => False
  | formula.atomic_prop p => M.valuation w p
  | ~ ψ => ¬ isSatisfied M w ψ
  | χ ↣ ψ => isSatisfied M w χ → isSatisfied M w ψ
  | formula.box i ψ => ∀ (v : M.world), (M.relation i w v → isSatisfied M v ψ)


def model1 : kripkeModel :=
{
  world := Char
  relation := ( λ i w v =>
  ((i = 1) ∧ (((w = 's') ∨ (w = 't')) ∧ ((v = 's') ∨ (v = 't'))) ∨ ((w = 'u') ∧ (v = 'u')))
  ∨
  ((i = 2) ∧ (((w = 's') ∨ (w = 'u')) ∧ ((v = 's') ∨ (v = 'u'))) ∨ ((w = 't') ∧ (v = 't'))) )

  valuation := (λ w c =>
  ((w = 's') ∨ (w = 'u')) ∧ (c = 'p')
  )
}

def test : Nat → Char → Char → Prop :=
  fun i w v =>
  ((i = 1) ∧ (((w = 's') ∨ (w = 't')) ∧ ((v = 's') ∨ (v = 't'))) ∨ ((w = 'u') ∧ (v = 'u')))
  ∨
  ((i = 2) ∧ (((w = 's') ∨ (w = 'u')) ∧ ((v = 's') ∨ (v = 'u'))) ∨ ((w = 't') ∧ (v = 't')))


#eval 1=1 ∧ 's'='s'


-- #eval model1.relation 1 's' 's' -- ?? help

-- #eval isSatisfied model1 's' ((K 2) (prop ('p'))) -- ?? help

def model2 : kripkeModel :=
{
  world := Char
  relation := (λ i w v => i = 1 ∧ w = 's' ∧ v = 's')
  valuation := (λ w c => w = 's' ∧ c = 'p')
}
