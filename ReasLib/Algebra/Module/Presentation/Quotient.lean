module

public import Mathlib.Algebra.Module.Presentation.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# A module presentation as a cokernel

This file exposes the canonical linear equivalence from the quotient by the range of a
presentation map to the presented module.
-/

universe u v w₀ w₁

namespace Module.Presentation

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A module presented by generators and relations is canonically the cokernel of its
presentation map. -/
@[stacks 05CS "a presentation as a cokernel"]
noncomputable def cokernelEquiv (P : Module.Presentation.{w₀, w₁} R M) :
    ((P.G →₀ R) ⧸ LinearMap.range P.map) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ P.range_map).trans P.toIsPresentation.linearEquiv

/-- The cokernel equivalence sends the class of a free linear combination through the
presentation map to `M`. -/
@[simp]
theorem cokernelEquiv_mk (P : Module.Presentation.{w₀, w₁} R M) (x : P.G →₀ R) :
    P.cokernelEquiv (Submodule.Quotient.mk x) = P.π x := by
  simp only [cokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  change P.toIsPresentation.linearEquiv (P.toRelations.toQuotient x) = P.π x
  rw [P.toIsPresentation.linearEquiv_apply,
    P.toSolution.fromQuotient_toQuotient]

/-- The cokernel equivalence sends the class of a free generator to its value in the presented
module. -/
@[simp]
theorem cokernelEquiv_mk_single (P : Module.Presentation.{w₀, w₁} R M) (g : P.G) :
    P.cokernelEquiv (Submodule.Quotient.mk (Finsupp.single g 1)) = P.var g := by
  simp

end Module.Presentation
