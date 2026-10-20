/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.LinearMap.Quotient
public import ReasLib.Algebra.Module.Presentation.Quotient

@[expose] public section

/-!
# Dual-number modules attached to module presentations

This file specializes the linear-map construction to an arbitrary module presentation. The
quotient computation is explicit and does not choose an equivalence from an existence theorem.
-/

universe u v w₀ w₁

open scoped DualNumber

namespace ModuleCat.DualNumber.Presentation

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The dual-number module attached to the relation map of a module presentation. -/
@[stacks 05CS "dual-number module of a presentation"]
noncomputable def of (P : Module.Presentation.{w₀, w₁} R M) :
    ModuleCat.{max u w₀ w₁} R[ε] :=
  ModuleCat.DualNumber.ofLinearMap P.map

/-- Modulo its square-zero endomorphism, the dual-number module of `P` is the product of the
relation module with the module presented by `P`. -/
@[stacks 05CS "quotient of the presentation module"]
noncomputable def quotientEquiv (P : Module.Presentation.{w₀, w₁} R M) :
  ModuleCat.DualNumber.epsQuotient (of P) ≃ₗ[R]
      (P.R →₀ R) × M :=
  (ModuleCat.DualNumber.OfLinearMap.epsQuotientEquiv P.map).trans
    ((LinearEquiv.refl R (P.R →₀ R)).prodCongr P.cokernelEquiv)

set_option backward.isDefEq.respectTransparency false in
/-- The quotient equivalence associated to a presentation sends a representative to its relation
coordinate and the image of its generator coordinate in the presented module. -/
@[simp]
theorem quotientEquiv_mk (P : Module.Presentation.{w₀, w₁} R M)
    (x : (P.R →₀ R) × (P.G →₀ R)) :
    quotientEquiv P (Submodule.Quotient.mk x) = (x.1, P.π x.2) := by
  change ((LinearEquiv.refl R (P.R →₀ R)).prodCongr P.cokernelEquiv)
      (ModuleCat.DualNumber.OfLinearMap.epsQuotientEquiv P.map
        (Submodule.Quotient.mk x)) =
    (x.1, P.π x.2)
  rw [ModuleCat.DualNumber.OfLinearMap.epsQuotientEquiv_mk]
  change (x.1, P.cokernelEquiv (Submodule.Quotient.mk x.2)) =
    (x.1, P.π x.2)
  rw [P.cokernelEquiv_mk]

/-- The inverse presentation quotient equivalence sends `(a, P.π b)` back to the class of
`(a, b)`. -/
@[simp]
theorem quotientEquiv_symm_π (P : Module.Presentation.{w₀, w₁} R M)
    (a : P.R →₀ R) (b : P.G →₀ R) :
    (quotientEquiv P).symm (a, P.π b) =
      (Submodule.Quotient.mk (a, b) :
        ModuleCat.DualNumber.epsQuotient (of P)) := by
  apply (quotientEquiv P).injective
  simp

end ModuleCat.DualNumber.Presentation
