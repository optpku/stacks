module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Compatibility check for the local purity predicate. -/
#check (AlgebraicGeometry.PuncturedSpectrum.HasPurity :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A], Prop)

/- Compatibility check for the local purity extension criterion. -/
#check (AlgebraicGeometry.PuncturedSpectrum.hasPurity_iff :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    AlgebraicGeometry.PuncturedSpectrum.HasPurity A ↔
      ∀ V : AlgebraicGeometry.Scheme.FiniteEtale
          (AlgebraicGeometry.PuncturedSpectrum.scheme A),
        ∃ Y : AlgebraicGeometry.Scheme.FiniteEtale
            (AlgebraicGeometry.Spec (CommRingCat.of A)),
          Nonempty
            ((AlgebraicGeometry.Scheme.finiteEtaleBaseChange
              (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A).ι).obj Y ≅ V))

end AlgebraicGeometry.PuncturedSpectrum
