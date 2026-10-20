module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived

/-! # Derived adjunction of degree-zero étale pullback inclusion

The continuous functor obtained by pulling back an étale object to degree zero and
including it in the total site induces an adjunction on bounded-below derived categories.
This construction is distinct from the total étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Abelian sheaf pullback along the degree-zero pullback inclusion preserves finite limits. -/
instance inverseImage_preservesFiniteLimits_addCommGrp :
    PreservesFiniteLimits ((augmentationFunctor U a).sheafPullback AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)) :=
  sorry

/-- Abelian sheaf pullback along the degree-zero pullback inclusion preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits_addCommGrp :
    PreservesFiniteColimits ((augmentationFunctor U a).sheafPullback AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)) :=
  sorry

/-- The exact abelian sheaf pullback along the degree-zero pullback inclusion. -/
def inverseImageExact :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of ((augmentationFunctor U a).sheafPullback AddCommGrpCat.{u + 1}
    (spacesEtaleTopology X) (spacesEtaleTotalTopology U))

/-- Continuous direct image along the degree-zero pullback inclusion admits a
bounded-below right-derived functor. -/
instance directImage_hasRightDerivedFunctor :
    ((augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- The bounded-below derived action of degree-zero abelian sheaf pullback. -/
def plusInverseImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (inverseImageExact a)

/-- The bounded-below right-derived continuous direct image along degree-zero pullback inclusion. -/
def plusDirectImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right
    ((augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))

/-- The bounded-below derived adjunction induced by the degree-zero pullback inclusion. -/
def plusAdjunction : plusInverseImage a ⊣ plusDirectImage a :=
  Adjunction.Derived.Plus.adjunction (inverseImageExact a)
    ((augmentationFunctor U a).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
    ((augmentationFunctor U a).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))

/-- The unit of the bounded-below derived adjunction of the degree-zero pullback inclusion. -/
def plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ⟶
      plusInverseImage a ⋙ plusDirectImage a :=
  (plusAdjunction a).unit

end AlgebraicGeometry.AlgebraicSpace.Simplicial
