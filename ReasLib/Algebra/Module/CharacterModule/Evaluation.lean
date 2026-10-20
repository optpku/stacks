module

public import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Evaluation into the double character module

The primary evaluation map is additive and therefore independent of any
chosen scalar ring. A commutative-ring linear view is supplied separately.

@stack 01DB
-/

universe u v

namespace CharacterModule

/-- Evaluation of additive characters gives a canonical additive map into
the double character module. -/
@[stacks 01DB "evaluation into the double character module"]
def eval {A : Type v} [AddCommGroup A] :
    A →+ CharacterModule (CharacterModule A) :=
  AddMonoidHom.eval

/-- Double-character evaluation applies the chosen character to the chosen
element. -/
@[simp]
theorem eval_apply {A : Type v} [AddCommGroup A]
    (a : A) (χ : CharacterModule A) : eval a χ = χ a := sorry
/- Proof strategy: unfold `eval`; this is the application rule for
`AddMonoidHom.eval`. -/

/-- Evaluation into the double character module is injective for every
additive commutative group. -/
@[stacks 01DB "injectivity of character evaluation"]
theorem eval_injective {A : Type v} [AddCommGroup A] :
    Function.Injective (eval : A →+ CharacterModule (CharacterModule A)) := sorry
/- Proof strategy: if every character vanishes on `a`, apply
`CharacterModule.eq_zero_of_character_apply`. -/

section Linear

variable (R : Type u) [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Evaluation respects the canonical commutative-ring action on the double
character module. -/
@[stacks 01DB "linearity of commutative character evaluation"]
theorem eval_map_smul (r : R) (m : M) : eval (r • m) = r • eval m := sorry
/- Proof strategy: extensionality at a character and two applications of
`CharacterModule.smul_apply`. -/

/-- The commutative-ring linear form of character evaluation. -/
@[stacks 01DB "linear double-character evaluation"]
def evalLinear : M →ₗ[R] CharacterModule (CharacterModule M) :=
  { (eval : M →+ CharacterModule (CharacterModule M)) with
    map_smul' := eval_map_smul R }

/-- Linear character evaluation has the same pointwise formula. -/
@[simp]
theorem evalLinear_apply (m : M) (χ : CharacterModule M) :
    evalLinear R m χ = χ m := sorry
/- Proof strategy: unfold `evalLinear` and apply `eval_apply`. -/

/-- The commutative-ring linear evaluation map is injective. -/
theorem evalLinear_injective : Function.Injective (evalLinear R :
    M →ₗ[R] CharacterModule (CharacterModule M)) := sorry
/- Proof strategy: use `eval_injective`; `evalLinear` has the same underlying
function as `eval`. -/

end Linear

end CharacterModule
