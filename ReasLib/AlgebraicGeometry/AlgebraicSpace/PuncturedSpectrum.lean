module

public import Mathlib.RingTheory.LocalRing.Defs
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# The punctured spectrum as an algebraic space

For a local ring `A`, the scheme `Spec(A)` and its open complement
`U = Spec(A) \ {𝔪}` are algebraic spaces over `Spec(A)`, and the open
immersion `U ⟶ Spec(A)` is the Yoneda image of the scheme-level open
immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme `Spec(A)` as an algebraic space over itself. -/
def specSpace (A : Type u) [CommRing A] : AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))

/-- `specSpace A` is `ofOver` of the identity slice of `Spec(A)`. -/
theorem specSpace_eq (A : Type u) [CommRing A] :
    specSpace A = ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))) :=
  sorry

/-- The punctured spectrum `U = Spec(A) \ {𝔪}` as an algebraic space over
`Spec(A)`. -/
def puncturedSpace (A : Type u) [CommRing A] [IsLocalRing A] :
    AlgebraicSpace (Spec (CommRingCat.of A)) :=
  ofOver (Over.mk (PuncturedSpectrum.puncturedOpen A).ι)

/-- `puncturedSpace A` is `ofOver` of the open immersion of the punctured
spectrum. -/
theorem puncturedSpace_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    puncturedSpace A = ofOver (Over.mk (PuncturedSpectrum.puncturedOpen A).ι) :=
  sorry

/-- The open immersion `U ⟶ Spec(A)` of algebraic spaces over `Spec(A)`. -/
def puncturedι (A : Type u) [CommRing A] [IsLocalRing A] :
    puncturedSpace A ⟶ specSpace A :=
  ofOverMap
    (Over.homMk (PuncturedSpectrum.puncturedOpen A).ι
      (Category.comp_id (PuncturedSpectrum.puncturedOpen A).ι))

/-- `puncturedι A` is `ofOverMap` of the scheme-level open immersion of the
punctured spectrum. -/
theorem puncturedι_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    puncturedι A =
      ofOverMap
        (Over.homMk (PuncturedSpectrum.puncturedOpen A).ι
          (Category.comp_id (PuncturedSpectrum.puncturedOpen A).ι)) :=
  sorry

/-- The comparison `puncturedι A` is an open immersion of algebraic spaces. -/
instance instIsOpenImmersion_puncturedι (A : Type u) [CommRing A] [IsLocalRing A] :
    IsOpenImmersion (puncturedι A) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
