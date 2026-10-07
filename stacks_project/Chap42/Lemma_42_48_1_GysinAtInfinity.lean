module

public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import stacks_project.Chap42.Lemma_42_35_4_OpenRestriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- The canonical Gysin-at-infinity class has its complete public type through this
compatibility module. -/
#check (AlgebraicGeometry.BivariantClass.gysinAtInfinity :
  ∀ {S W : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)],
    BivariantClass δ (GysinAtInfinity.infinityToX X b) 0)

end AlgebraicGeometry.BivariantClass
