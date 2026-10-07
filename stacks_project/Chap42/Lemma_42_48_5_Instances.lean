module

public import stacks_project.Chap42.Lemma_42_48_1_GysinAtInfinity

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
