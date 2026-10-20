module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism

/-!
# Lower shriek of abelian sheaves on categories fibred in groupoids

Inverse image on abelian sheaves has a canonical left adjoint for each standard
topology. For a faithful morphism whose source has equalizers, this left adjoint
is exact and inverse image preserves injective objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The canonical lower shriek on abelian sheaves is left adjoint to inverse image
along a morphism of categories fibred in groupoids for every standard topology. -/
noncomputable def abelianLowerShriekAdjunction
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
    [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    ((toCartesianBasedFunctor f).toFunctor.sheafPullback AddCommGrpCat.{u + 1}
      (X.associatedTopology τ) (Y.associatedTopology τ)) ⊣
      ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)) :=
  (toCartesianBasedFunctor f).toFunctor.sheafAdjunctionContinuous
    AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)

/-- Lower shriek on abelian sheaves along a faithful morphism of categories fibred
in groupoids whose source has equalizers is exact for every standard topology. -/
theorem sheafPullback_exact
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    exactFunctor
      (Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
      (Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})
      ((toCartesianBasedFunctor f).toFunctor.sheafPullback AddCommGrpCat.{u + 1}
        (X.associatedTopology τ) (Y.associatedTopology τ)) :=
  sorry

/-- Inverse image on abelian sheaves along a faithful morphism of categories fibred
in groupoids whose source has equalizers preserves injective objects for every
standard topology. -/
instance sheafPushforwardContinuous_preservesInjectiveObjects
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ)
        (Y.associatedTopology τ)).PreservesInjectiveObjects :=
  sorry

end AlgebraicGeometry.GroupoidsOver
