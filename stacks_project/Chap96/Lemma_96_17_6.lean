/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek

/-!
# Lower shriek of modules on categories fibred in groupoids

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` has a left
adjoint `f_!` to inverse image on modules. If the 1-morphism is faithful and
the source has equalizers, then `f_!` is exact and inverse image preserves
injective modules, for every standard topology `τ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 96.17.6 (1): the inverse image `f^*` of modules along a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf` has a left adjoint `f_!` for
every standard topology `τ`. -/
@[stacks 06X2, instance]
instance associatedModuleInverseImage_isRightAdjoint
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    (associatedModuleInverseImage f τ).IsRightAdjoint :=
  sorry

/-- Lemma 96.17.6 (2): the module lower shriek `f_!` agrees with the abelian
lower shriek of Lemma 96.17.5 on underlying abelian sheaves. -/
@[stacks 06X2, instance]
instance associatedModuleLowerShriek_underlyingComparison_isIso
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
    [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    IsIso (associatedModuleLowerShriek_underlyingComparison f τ) :=
  sorry

/-- Lemma 96.17.6 (3): if a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful and `X` has equalizers, then the
associated module lower shriek `f_!` is exact for every standard topology `τ`. -/
@[stacks 06X2]
theorem associatedModuleLowerShriek_exact
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    exactFunctor
      (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))
      (SheafOfModules.{u + 1} (associatedStructureSheaf Y τ))
      (associatedModuleLowerShriek f τ) :=
  sorry

/-- Lemma 96.17.6 (4): if a 1-morphism `f : X ⟶ Y` of categories fibred in
groupoids over `(Sch/S)_fppf` is faithful and `X` has equalizers, then inverse
image of modules preserves injective objects for every standard topology `τ`. -/
@[stacks 06X2, instance]
instance associatedModuleInverseImage_preservesInjectiveObjects
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}] :
    (associatedModuleInverseImage f τ).PreservesInjectiveObjects :=
  sorry

/-- Objectwise form of module inverse image preserving injectives. -/
theorem injective_associatedModuleInverseImage
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
    [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]
    (I : SheafOfModules.{u + 1} (associatedStructureSheaf Y τ)) [Injective I] :
    Injective ((associatedModuleInverseImage f τ).obj I) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
