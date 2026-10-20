module

public import ReasLib.Algebra.Module.Graded.LocallyFinite.Kernel
import StacksCheckRecall

/-!
# Kernel of a map of locally finite graded modules

If `A` is Noetherian, the kernel of a degree-preserving map of locally finite ℤ-graded
`A`-modules is again locally finite.
-/

@[expose] public section

universe u v w

open GradedModule

namespace GradedModule

/- Exercise 111.26.7: over a Noetherian ring, the kernel of a degree-preserving map of
locally finite graded modules is locally finite. -/
@[stacks 02E5] #check (GradedModule.LocallyFinite.ker :
  {A : Type u} → {M : Type v} → {N : Type w} →
    [CommRing A] → [IsNoetherianRing A] → [AddCommGroup M] → [Module A M] →
    [AddCommGroup N] → [Module A N] →
    {ℳ : ℤ → Submodule A M} → {𝒩 : ℤ → Submodule A N} →
    [DirectSum.Decomposition ℳ] → [DirectSum.Decomposition 𝒩] →
    [LocallyFinite ℳ] → [LocallyFinite 𝒩] →
    (f : MapsTo A ℳ 𝒩 (id : ℤ → ℤ)) →
    LocallyFinite (DirectSum.Decomposition.submoduleGrading ℳ
      (LinearMap.ker (MapsTo.toLinearMap f))))

end GradedModule
