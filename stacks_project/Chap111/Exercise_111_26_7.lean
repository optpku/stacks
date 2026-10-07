module

public import stacks_project.Chap111.Definition_111_26_2_LocallyFinite
public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.Graded.Submodule
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel of a map of locally finite graded modules

If `A` is Noetherian, the kernel of a degree-preserving map of locally finite ℤ-graded
`A`-modules is again locally finite.
-/

@[expose] public section

universe u v w

open GradedModule

namespace GradedModule

/-- Exercise 111.26.7: if `A` is Noetherian, the kernel of a map of locally finite graded
`A`-modules is locally finite. -/
@[stacks 02E5]
instance LocallyFinite.ker {A : Type u} {M : Type v} {N : Type w}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ℳ : ℤ → Submodule A M} {𝒩 : ℤ → Submodule A N}
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    [LocallyFinite ℳ] [LocallyFinite 𝒩] (f : MapsTo A ℳ 𝒩 (id : ℤ → ℤ)) :
    LocallyFinite (DirectSum.Decomposition.submoduleGrading ℳ
      (LinearMap.ker (MapsTo.toLinearMap f))) := sorry

/-- The intersection of a degree piece with the kernel of a degree-preserving map is a finite
`A`-module. -/
instance LocallyFinite.finite_inf_ker {A : Type u} {M : Type v} {N : Type w}
    [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {ℳ : ℤ → Submodule A M} {𝒩 : ℤ → Submodule A N}
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
    [LocallyFinite ℳ] [LocallyFinite 𝒩] (f : MapsTo A ℳ 𝒩 (id : ℤ → ℤ)) (n : ℤ) :
    Module.Finite A (ℳ n ⊓ LinearMap.ker (MapsTo.toLinearMap f) : Submodule A M) := sorry

end GradedModule
