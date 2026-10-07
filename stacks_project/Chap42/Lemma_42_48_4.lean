module

public import stacks_project.Chap42.Lemma_42_48_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-- The degree-normalized Gysin pullback along the infinity-fibre inclusion. -/
noncomputable def gysinPullback
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] (k : ℤ) :
    RelativeChow δ (compactification X b) (k + 1) →+
      RelativeChow δ (infinityFiber X b) k :=
  (ChowCohomology.castDegree δ (gysinDegree k)).comp
    (ChowGroup.gysin δ (compactification X b) (infinityLineBundle X b)
      (infinitySection X b) (k + 1))

/-- `gysinPullback` is zero-scheme Gysin followed by the canonical grading transport. -/
theorem gysinPullback_def
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] (k : ℤ) :
    gysinPullback δ X b k =
      (ChowCohomology.castDegree δ (gysinDegree k)).comp
        (ChowGroup.gysin δ (compactification X b) (infinityLineBundle X b)
          (infinitySection X b) (k + 1)) := sorry

/-- The degree-normalized action of the Gysin-at-infinity class on the base square. -/
noncomputable def capAtBase
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)] (k : ℤ) :
    RelativeChow δ (Over.mk X.hom) k →+ RelativeChow δ (infinityFiber X b) k :=
  (ChowCohomology.castDegree δ (Int.sub_zero k)).comp
    ((BivariantClass.gysinAtInfinity δ X b).cap (𝟙 (infinityFiber X b))
      (infinityToX X b) (𝟙 (Over.mk X.hom))
      (IsPullback.id_horiz (infinityToX X b).left) k)

/-- `capAtBase` is the canonical cap action of `gysinAtInfinity`, with degree normalized. -/
theorem capAtBase_def
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)] (k : ℤ) :
    capAtBase δ X b k =
      (ChowCohomology.castDegree δ (Int.sub_zero k)).comp
        ((BivariantClass.gysinAtInfinity δ X b).cap (𝟙 (infinityFiber X b))
          (infinityToX X b) (𝟙 (Over.mk X.hom))
          (IsPullback.id_horiz (infinityToX X b).left) k) := sorry

/-- The canonical map from the infinity fibre to `X` is proper. -/
instance infinityToXIsProper
    {S W : Scheme.{u}} (X : Over S)
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] :
    IsProper (infinityToX X b).left := sorry

/-- Lemma 42.48.4: capping with the Gysin-at-infinity class after proper pushforward
from `W∞` to `X` recovers the Gysin pullback along `i∞ : W∞ ⟶ W`. -/
@[stacks 0FAR]
theorem cap_map_gysin
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ affinePart X)] (k : ℤ) :
    (capAtBase δ X b k).comp
        ((ChowGroup.map δ (infinityFiber X b) (Over.mk X.hom)
          (infinityToX X b) k).comp (gysinPullback δ X b k)) =
      gysinPullback δ X b k := sorry

end AlgebraicGeometry.BivariantClass.GysinAtInfinity
