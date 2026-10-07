module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
import StacksCheckRecall

/-!
# Lower shriek of abelian sheaves on categories fibred in groupoids

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has a left adjoint
`f_!` to inverse image on abelian sheaves. If the 1-morphism is faithful and the source
has equalizers, then `f_!` is exact and inverse image preserves injective objects, for
every standard topology `τ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

section

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
variable [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
variable (ℱ : Sheaf (X.associatedTopology τ) AddCommGrpCat.{u + 1})
variable (𝒢 : Sheaf (Y.associatedTopology τ) AddCommGrpCat.{u + 1})

/- Lemma 96.17.5 (1): the inverse image `f⁻¹` of abelian sheaves along a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf` has a left adjoint `f_!` for every
standard topology `τ`. -/
@[stacks 06X1]
#check (((toCartesianBasedFunctor f).toFunctor.sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)).homEquiv ℱ 𝒢 :
    (((toCartesianBasedFunctor f).toFunctor.sheafPullback
        AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)).obj ℱ ⟶ 𝒢) ≃
      (ℱ ⟶ ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (X.associatedTopology τ) (Y.associatedTopology τ)).obj 𝒢))

end

/-- Lemma 96.17.5 (2): if a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf` is faithful and `X` has equalizers, then the associated lower
shriek `f_!` of abelian sheaves is exact for every standard topology `τ`. -/
@[stacks 06X1]
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

/-- Lemma 96.17.5 (3): if a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids
over `(Sch/S)_fppf` is faithful and `X` has equalizers, then inverse image of abelian
sheaves preserves injective objects for every standard topology `τ`. -/
@[stacks 06X1, instance]
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
