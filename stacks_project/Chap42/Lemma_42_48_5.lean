module

public import stacks_project.Chap42.Lemma_42_48_1
public import stacks_project.Chap42.Lemma_42_48_5_Instances
public import stacks_project.Chap42.Remark_42_33_6_Commutation

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Lemma 42.48.5: every bivariant class for a locally finite-type morphism to `X`
commutes with the Gysin-at-infinity class on the canonical fibre product over `X`. -/
@[stacks 0FAS]
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
