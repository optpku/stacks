module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.DegreeZeroDerived
public import stacks_project.Chap85.Lemma_85_33_1_Etale
public import stacks_project.Chap85.Lemma_85_33_2_Cartesian
public import stacks_project.Chap85.Lemma_85_33_2_Equivalence

/-! # Compatibility checks for the degree-zero étale derived adjunction -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

noncomputable section

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Direct image of abelian sheaves along the degree-zero pullback inclusion is additive. -/
instance AlgebraicGeometry.AlgebraicSpace.Simplicial.directImage_additive_addCommGrp :
    (directImage U AddCommGrpCat.{u + 1} a).Additive := by
  unfold directImage
  exact Functor.sheafPushforwardContinuous_additive (augmentationFunctor U a)
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.inverseImageExact a :
  Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
    Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

#check (Eq.refl ((augmentationFunctor U a).sheafPullback AddCommGrpCat.{u + 1}
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U)) :
  (inverseImageExact a).obj = (augmentationFunctor U a).sheafPullback AddCommGrpCat.{u + 1}
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusInverseImage a :
  DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusDirectImage a :
  DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusAdjunction a :
  plusInverseImage a ⊣ plusDirectImage a)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusDerivedUnit a :
  𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ⟶
    plusInverseImage a ⋙ plusDirectImage a)

#check (Eq.refl (plusAdjunction a).unit : plusDerivedUnit a = (plusAdjunction a).unit)
