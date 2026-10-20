module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Affine.QuasiCoherent

/-!
# Algebraization from ideal-power thickenings

Equivalences for proper-support completion on all positive-power thickenings
and a uniformly torsion approximation imply algebraizability.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Over a complete Noetherian affine base, a proper-support coherent formal
module is algebraizable if proper-support completion is an equivalence on every
positive-power `K`-thickening and it admits an approximation by a proper-support
coherent module whose stagewise kernels and cokernels are uniformly annihilated
by one positive power of `K`. -/
theorem mem_essImage_of_thickening_equivalences_and_torsion_approximation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)]
    (K : IdealSubobject X) [IsQuasiCoherent K]
    (hThickeningEquiv : ∀ e : ℕ+,
      (idealPowerCompletionFunctor (SchemeRealization.toBase X)
        (pullbackIdeal I (SchemeRealization.toBase X)) K e).IsEquivalence)
    (E : CoherentFormalProperSupportOver (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X)))
    (H : CoherentProperSupportOver (SchemeRealization.toBase X))
    (alpha : E ⟶ (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).obj H)
    (halpha : CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha.hom) :
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).essImage E := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
