module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.NeighborhoodSections

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

open Scheme Scheme.Modules Scheme.ModuleDerived.DerivedCompletion
  RingedSpace.Module.Derived

/- Lemma 52.11.3: the associated-point dimension bound makes the canonical
neighborhood-section comparison an isomorphism of finite modules. -/
@[stacks 0DXR] #check (AlgebraicGeometry.PuncturedSpectrum.neighborhoodComparison_isIso_finite :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h_dualizing : DerivedCategory.HasCanonicalDualizingComplex A)
    (I : Ideal A) [IsAdicComplete I A]
    (F : RingedSpace.Coh (scheme A).toRingedSpace)
    (h_dimension : ∀ x : scheme A, x ∈ associatedPoints F.obj →
      ((Ideal.LocalCohomology.dimension I
          I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        WithBot.map (WithTop.map Int.ofNat)
          (ringKrullDim (A ⧸ x.1.asIdeal))),
    IsIso (neighborhoodQuotientCohomologyComparison A I
        ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj)) ∧
      Module.Finite A
        ((limit (quotientCohomologySystem (puncturedOpen A).ι I
          ((Scheme.Modules.fromRingedSpace (scheme A)).obj F.obj) 0)) :
            ModuleCat.{u} A))

end AlgebraicGeometry.PuncturedSpectrum
