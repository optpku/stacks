module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.RingTheory.DualNumberPair

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace DualNumberPair

variable (R : Type u) [CommRing R]

noncomputable section

/-- The morphism from `Spec R` to `Spec (DualNumber R)` induced by the
coefficient projection of the dual-number algebra. -/
def fromClosedPoint :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)

/-- The spectrum morphism induced by the first projection of `DualNumberPair R`. -/
def inl :
    Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of (DualNumberPair R)) :=
  Spec.map (CommRingCat.ofHom (projFst R).toRingHom)

/-- The spectrum morphism induced by the second projection of `DualNumberPair R`. -/
def inr :
    Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of (DualNumberPair R)) :=
  Spec.map (CommRingCat.ofHom (projSnd R).toRingHom)

/-- For a field `K`, the spectra of the two dual-number directions form a
pushout square over `Spec K`. -/
theorem spec_isPushout (K : Type u) [Field K] :
    IsPushout (fromClosedPoint K) (fromClosedPoint K) (inl K) (inr K) :=
  sorry

end

end DualNumberPair
