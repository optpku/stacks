module

public import Mathlib.Algebra.Algebra.Defs
public import ReasLib.Algebra.Ring.CommutatorQuotient
public import stacks_project.Chap64.Definition_64_4_1_Natural

/-!
# A-module structure on the additive commutator quotient

This leaf owns the `A`-module structure on `Λ♮` induced by an algebra
`Algebra A Λ`. The action on classes is descent of
`a • λ = algebraMap A Λ a * λ` along `CommutatorQuotient.mk`.
-/

@[expose] public section

noncomputable section

universe u v

open Ring
open scoped Ring

namespace Ring.CommutatorQuotient

variable {A : Type u} {Λ : Type v} [CommRing A] [Ring Λ] [Algebra A Λ]

/- The canonical `A`-linear projection `Λ →ₗ[A] Λ♮`. -/
#check (mkLinearMap : ∀ (A : Type u) (Λ : Type v) [CommRing A] [Ring Λ]
  [Algebra A Λ], Λ →ₗ[A] CommutatorQuotient Λ)

end Ring.CommutatorQuotient
