module

public import ReasLib.Algebra.Module.Graded.LocallyFinite
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.Graded.Submodule
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Kernels of locally finite graded modules

The inherited grading on the kernel of a degree-preserving linear map has finite pieces
over a Noetherian ring.
-/

@[expose] public section

universe u v w

namespace GradedModule

/-- Over a Noetherian ring, the intersection of a finite graded piece with the kernel of a
degree-preserving map between locally finite graded modules is a finite module. -/
instance LocallyFinite.finite_inf_ker {A : Type u} {M : Type v} {N : Type w}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ℳ : ℤ → Submodule A M} {𝒩 : ℤ → Submodule A N}
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    [LocallyFinite ℳ] [LocallyFinite 𝒩] (f : MapsTo A ℳ 𝒩 (id : ℤ → ℤ)) (n : ℤ) :
    Module.Finite A (ℳ n ⊓ LinearMap.ker (MapsTo.toLinearMap f) : Submodule A M) := sorry

/-- The grading inherited by the kernel of a degree-preserving map between locally finite
graded modules over a Noetherian ring is locally finite. -/
instance LocallyFinite.ker {A : Type u} {M : Type v} {N : Type w}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ℳ : ℤ → Submodule A M} {𝒩 : ℤ → Submodule A N}
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    [LocallyFinite ℳ] [LocallyFinite 𝒩] (f : MapsTo A ℳ 𝒩 (id : ℤ → ℤ)) :
    LocallyFinite (DirectSum.Decomposition.submoduleGrading ℳ
      (LinearMap.ker (MapsTo.toLinearMap f))) := sorry

end GradedModule
