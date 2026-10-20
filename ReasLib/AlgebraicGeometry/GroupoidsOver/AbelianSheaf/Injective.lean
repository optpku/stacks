module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Injective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import Mathlib.CategoryTheory.Sites.CoverLifting

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Direct image along a morphism of categories fibred in groupoids preserves injective
abelian sheaves for every standard topology. -/
instance sheafPushforwardCocontinuous_preservesInjectiveObjects
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P] :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ)
        (Y.associatedTopology τ)).PreservesInjectiveObjects :=
  sorry

/-- The direct image of an injective abelian sheaf along a morphism of categories fibred
in groupoids is injective for every standard topology. -/
theorem injective_sheafPushforwardCocontinuous
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
    (I : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1}) [Injective I] :
    Injective
      (((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (X.associatedTopology τ)
          (Y.associatedTopology τ)).obj I) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
