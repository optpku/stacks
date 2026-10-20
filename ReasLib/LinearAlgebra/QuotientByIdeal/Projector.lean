/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.LinearMap.Projector
public import Mathlib.LinearAlgebra.Isomorphisms
public import ReasLib.LinearAlgebra.QuotientByIdeal
public import ReasLib.LinearAlgebra.QuotientByIdeal.Scalar
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Projector ranges modulo an ideal

This leaf owns the first-isomorphism comparison for an idempotent range after quotienting by an
ideal multiple.  The ambient quotient map is kept abstract: free-module presentations such as
`Finsupp` and `Fin n → R` belong to their own leaves and only supply the three hypotheses below.
-/

@[expose] public section

universe u v w

namespace LinearMap.QuotientByIdeal

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-! The public map and quotient equivalence are separated so consumers can use the induced map,
its kernel, or the final equivalence independently. -/

/-- Intertwining sends the range of the source endomorphism into the range of the target. -/
@[stacks 07LV "projector range map membership"]
theorem rangeMap_mem
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hintertwine : q.comp p = p'.comp q) (x : LinearMap.range p) :
    q x ∈ LinearMap.range p' := sorry

/-- The canonical map between the ranges of intertwined endomorphisms. -/
@[stacks 07LV "projector range map"]
noncomputable def rangeMap
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hintertwine : q.comp p = p'.comp q) :
    LinearMap.range p →ₗ[R] LinearMap.range p' :=
  (q.comp (LinearMap.range p).subtype).codRestrict (LinearMap.range p')
    (rangeMap_mem q p p' hintertwine)

/-- Evaluation of the induced range map on the underlying module. -/
@[simp]
theorem rangeMap_apply_val
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hintertwine : q.comp p = p'.comp q) (x : LinearMap.range p) :
    (rangeMap q p p' hintertwine x : N) = q x := sorry

/-- Surjectivity of the induced range map follows from surjectivity of the ambient map. -/
@[stacks 07LV "projector range map surjective"]
theorem rangeMap_surjective
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hintertwine : q.comp p = p'.comp q) (hq : Function.Surjective q) :
    Function.Surjective (rangeMap q p p' hintertwine) := sorry

/-- The kernel of the induced range map is the pullback of the ambient kernel. -/
@[stacks 07LV "projector range map kernel"]
theorem rangeMap_ker
    (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hintertwine : q.comp p = p'.comp q) :
    LinearMap.ker (rangeMap q p p' hintertwine) =
      Submodule.comap (LinearMap.range p).subtype (LinearMap.ker q) := sorry

/-- For an idempotent source endomorphism, the induced kernel is the ideal multiple of its range
when the ambient kernel is `I • ⊤`. -/
@[stacks 07LV "projector range map ideal kernel"]
theorem rangeMap_ker_eq_smul_top
    (I : Ideal R) (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hp : IsIdempotentElem p) (hker : LinearMap.ker q = I • (⊤ : Submodule R M))
    (hintertwine : q.comp p = p'.comp q) :
    LinearMap.ker (rangeMap q p p' hintertwine) =
      I • (⊤ : Submodule R (LinearMap.range p)) := sorry

/-- The quotient of an idempotent range by an ideal multiple, identified with the target range of
an intertwined endomorphism. -/
@[stacks 07LV "projector range quotient equivalence"]
noncomputable def rangeEquivOfIdeal
    (I : Ideal R) (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hp : IsIdempotentElem p) (hq : Function.Surjective q)
    (hker : LinearMap.ker q = I • (⊤ : Submodule R M))
    (hintertwine : q.comp p = p'.comp q) :
    ((LinearMap.range p) ⧸ (I • (⊤ : Submodule R (LinearMap.range p)))) ≃ₗ[R]
      LinearMap.range p' :=
  (Submodule.quotEquivOfEq _ _
      (rangeMap_ker_eq_smul_top I q p p' hp hker hintertwine).symm).trans
    ((rangeMap q p p' hintertwine).quotKerEquivOfSurjective
      (rangeMap_surjective q p p' hintertwine hq))

/-- The quotient-range equivalence sends a representative to the induced range map. -/
@[simp, stacks 07LV "projector range quotient representative"]
theorem rangeEquivOfIdeal_apply_mk
    (I : Ideal R) (q : M →ₗ[R] N) (p : Module.End R M) (p' : Module.End R N)
    (hp : IsIdempotentElem p) (hq : Function.Surjective q)
    (hker : LinearMap.ker q = I • (⊤ : Submodule R M))
    (hintertwine : q.comp p = p'.comp q) (x : LinearMap.range p) :
    rangeEquivOfIdeal I q p p' hp hq hker hintertwine (Submodule.Quotient.mk x) =
      rangeMap q p p' hintertwine x := sorry

/-- Restricting quotient-ring scalars identifies `rangeEquivOfIdeal` with the target range
viewed as an `R`-module. -/
@[stacks 07LV "projector range restricted-scalar equivalence"]
noncomputable def rangeEquivOfIdeal_restrictScalars
    (I : Ideal R) [I.IsTwoSided]
    {N : Type w} [AddCommGroup N] [Module R N] [Module (R ⧸ I) N]
    [IsScalarTower R (R ⧸ I) N]
    (q : M →ₗ[R] N) (p : Module.End R M)
    (pbar : Module.End (R ⧸ I) N) (hp : IsIdempotentElem p)
    (hq : Function.Surjective q)
    (hker : LinearMap.ker q = I • (⊤ : Submodule R M))
    (hintertwine : q.comp p = (pbar.restrictScalars R).comp q) :
    ((LinearMap.range p) ⧸ (I • (⊤ : Submodule R (LinearMap.range p)))) ≃ₗ[R]
      (LinearMap.range pbar).restrictScalars R :=
  (rangeEquivOfIdeal I q p (pbar.restrictScalars R) hp hq hker hintertwine).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_restrictScalars (R := R) pbar))

/-- Quotient-ring-linear form of `rangeEquivOfIdeal`, with the target endomorphism given over the
quotient ring.  The public target is the natural quotient-linear range; the restricted-scalar
range is kept internal to the construction. -/
@[stacks 07LV "projector range quotient-ring equivalence"]
noncomputable def rangeEquivOverQuotient
    (I : Ideal R) [I.IsTwoSided]
    {N : Type w} [AddCommGroup N] [Module R N] [Module (R ⧸ I) N]
    [IsScalarTower R (R ⧸ I) N]
    (q : M →ₗ[R] N) (p : Module.End R M)
    (pbar : Module.End (R ⧸ I) N) (hp : IsIdempotentElem p)
    (hq : Function.Surjective q)
    (hker : LinearMap.ker q = I • (⊤ : Submodule R M))
    (hintertwine : q.comp p = (pbar.restrictScalars R).comp q) :
    ((LinearMap.range p) ⧸ (I • (⊤ : Submodule R (LinearMap.range p)))) ≃ₗ[R ⧸ I]
      LinearMap.range pbar :=
  (LinearEquiv.extendScalarsOfQuotient (R := R) (I := I)
      (rangeEquivOfIdeal_restrictScalars I q p pbar hp hq hker hintertwine)).trans
    (Submodule.restrictScalarsEquiv (S := R) (p := LinearMap.range pbar))

end LinearMap.QuotientByIdeal
