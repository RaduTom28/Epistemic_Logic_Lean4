set_option autoImplicit false

-- Definition of a formula in epistemic  logic

inductive formula where
| bottom: formula
| atomic_prop: Char → formula
| not: formula → formula
| implication: formula → formula → formula
| box: Nat → formula → formula


#check formula.implication (formula.atomic_prop 'p') (formula.box 1 (formula.atomic_prop 'q'))

--notations for constructors

def prop (c : Char) : formula := formula.atomic_prop c
prefix:80 "~" => formula.not
prefix:70 "K" => formula.box
infix:50 "↣" => formula.implication
notation "⊥" => formula.bottom

#check (K 1) (prop 'p')

-- defining conjunction and disjunction

def form_and (φ  ψ : formula) : formula := ~ (φ ↣ ~ψ)
infix:60 "⋏" => form_and

def form_or (φ  ψ : formula) : formula := (~φ) ↣ ψ
infix:60 "⋎" => form_or
