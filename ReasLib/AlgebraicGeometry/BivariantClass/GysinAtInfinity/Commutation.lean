module

public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-- The canonical morphism from the infinity fibre to `X` is locally of finite type. -/
instance infinityToXLocallyOfFiniteType
    {S W : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b] :
    LocallyOfFiniteType (infinityToX X b).left := sorry

end AlgebraicGeometry.BivariantClass.GysinAtInfinity

namespace AlgebraicGeometry.BivariantClass

/-- The Gysin-at-infinity class commutes with every bivariant class into the base. -/
theorem gysinAtInfinity_commute
    {S W : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ GysinAtInfinity.affinePart X)]
    {Y : Over S} [LocallyOfFiniteType Y.hom]
    (f : Y ⟶ Over.mk X.hom) [LocallyOfFiniteType f.left]
    (q : ℤ) (c : BivariantClass δ f q) :
    Commute δ f (GysinAtInfinity.infinityToX X b) c (gysinAtInfinity δ X b) := sorry

end AlgebraicGeometry.BivariantClass
