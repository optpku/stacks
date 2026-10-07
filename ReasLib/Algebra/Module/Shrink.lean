module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shrinking Linear Maps

This leaf owns the canonical conjugation of a linear map along
`Shrink.linearEquiv`. It keeps the target universe explicit through the
`Small` hypotheses and exposes map, exactness, and kernel transport APIs.
-/

@[expose] public section

universe u v w x z

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Conjugate an `R`-linear map by the canonical equivalences from shrunken modules. -/
@[stacks 00OF "shrunken linear map"]
noncomputable def shrink [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) :
    Shrink.{z} M →ₗ[R] Shrink.{z} N :=
  LinearEquiv.arrowCongrAddEquiv
    (Shrink.linearEquiv R M).symm
    (Shrink.linearEquiv R N).symm f

/-- Evaluation of a shrunken linear map through the canonical shrink equivalences. -/
@[simp]
theorem shrink_apply [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) (x : Shrink.{z} M) :
    shrink f x = (Shrink.linearEquiv R N).symm (f (Shrink.linearEquiv R M x)) := sorry

/-- The canonical shrink equivalences intertwine a linear map and its shrunken form. -/
theorem linearEquiv_comp_shrink [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) :
    (Shrink.linearEquiv R N).toLinearMap.comp (shrink f) =
      f.comp (Shrink.linearEquiv R M).toLinearMap := sorry

/-- Surjectivity is preserved by shrinking the source and target modules of a linear map. -/
theorem shrink_surjective [Small.{z} M] [Small.{z} N] {f : M →ₗ[R] N}
    (h_surjective : Function.Surjective f) :
    Function.Surjective (shrink f) := sorry

/-- Exactness is preserved by shrinking every module in a composable pair of linear maps. -/
theorem shrink_exact [Small.{z} M] [Small.{z} N] [Small.{z} P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h_exact : Function.Exact f g) :
    Function.Exact (shrink f) (shrink g) := sorry

/-- Mapping the kernel of a shrunken linear map along the canonical equivalence recovers the
original kernel. -/
theorem map_ker_shrink [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) :
    Submodule.map (Shrink.linearEquiv R M).toLinearMap (LinearMap.ker (shrink f)) =
      LinearMap.ker f := sorry

/-- The canonical shrink equivalence restricts to an equivalence of the corresponding kernels. -/
@[stacks 00OF "kernel equivalence for a shrunken linear map"]
noncomputable def shrinkKerEquiv [Small.{z} M] [Small.{z} N] (f : M →ₗ[R] N) :
    LinearMap.ker (shrink f) ≃ₗ[R] LinearMap.ker f :=
  (Shrink.linearEquiv R M).ofSubmodules _ _ (map_ker_shrink f)

end LinearMap
