module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.DualNumber

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber DualNumberPair

universe u

/- A typed compatibility check for the reusable coordinate-ring pullback. -/
#check (DualNumberPair.isPullback :
  ∀ (R : Type u) [CommRing R],
    IsPullback
      (CommRingCat.ofHom (DualNumberPair.projFst R).toRingHom)
      (CommRingCat.ofHom (DualNumberPair.projSnd R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom))

/- A typed compatibility check for the reusable closed-point spectrum map. -/
#check (DualNumberPair.fromClosedPoint :
  ∀ (R : Type u) [CommRing R],
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (DualNumber R)))
