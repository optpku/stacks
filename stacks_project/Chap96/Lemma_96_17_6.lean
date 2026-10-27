/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.LowerShriek
import StacksCheckRecall

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

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/- Lemma 96.17.6 (1): module lower shriek is left adjoint to module inverse image. -/
@[stacks 06X2] #check
  (AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek_adjunction f τ :
    AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek f τ ⊣
      AlgebraicGeometry.GroupoidsOver.associatedModuleInverseImage f τ)

section Comparison

variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (toCartesianBasedFunctor f).toFunctor.op.HasLeftKanExtension P]
variable [HasWeakSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]

/- Lemma 96.17.6 (2): the canonical comparison with lower shriek on abelian sheaves
is invertible. -/
@[stacks 06X2] #check
  (AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek_underlyingComparison_isIso f τ :
    IsIso (AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek_underlyingComparison f τ))

end Comparison

section Exactness

variable [Functor.Faithful (toFunctor f)] [HasEqualizers X.total]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseLeftKanExtension P]
variable [HasSheafify (Y.associatedTopology τ) AddCommGrpCat.{u + 1}]

/- Lemma 96.17.6 (3): for a faithful morphism with source equalizers, module lower
shriek is exact. -/
@[stacks 06X2] #check
  (AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek_exact f τ :
    exactFunctor
      (SheafOfModules.{u + 1} (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf X τ))
      (SheafOfModules.{u + 1} (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf Y τ))
      (AlgebraicGeometry.GroupoidsOver.associatedModuleLowerShriek f τ))

/- Lemma 96.17.6 (4): for a faithful morphism with source equalizers, module inverse
image preserves injective objects. -/
@[stacks 06X2] #check
  (AlgebraicGeometry.GroupoidsOver.associatedModuleInverseImage_preservesInjectiveObjects f τ :
    (AlgebraicGeometry.GroupoidsOver.associatedModuleInverseImage f τ).PreservesInjectiveObjects)

variable (I : SheafOfModules.{u + 1}
  (AlgebraicGeometry.GroupoidsOver.associatedStructureSheaf Y τ)) [Injective I]

-- The canonical objectwise consequence of preservation of injective objects.
#check (CategoryTheory.Functor.injective_obj
  (AlgebraicGeometry.GroupoidsOver.associatedModuleInverseImage f τ) I :
  Injective ((AlgebraicGeometry.GroupoidsOver.associatedModuleInverseImage f τ).obj I))

end Exactness

end AlgebraicGeometry.GroupoidsOver
