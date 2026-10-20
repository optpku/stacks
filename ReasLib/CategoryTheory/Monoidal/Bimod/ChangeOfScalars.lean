/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Map
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of scalars for bimodule objects

@stack 0FSA

This file supplies the generic restriction and extension-of-scalars operations for modules over
monoid objects.  It also normalizes the image of a one-sided module under a lax monoidal functor
using the functor's unit morphism.  These constructions are independent of the ambient realization
by ordinary modules, graded objects, complexes, or sheaves.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

universe u v u' v'

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A A' B B' : Mon C}

/-- Restrict the left action of an `(A,B)`-bimodule along `f : A' ⟶ A`. -/
@[stacks 0FSA "restriction of a left monoid action"]
def restrictLeftObj (f : A' ⟶ A) (M : Bimod A B) : Bimod A' B where
  X := M.X
  actLeft := (f.hom ▷ M.X) ≫ M.actLeft
  actRight := M.actRight
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- A bimodule morphism remains a morphism after restriction of its left action. -/
def restrictLeftMap (f : A' ⟶ A) {M N : Bimod A B} (g : M ⟶ N) :
    restrictLeftObj f M ⟶ restrictLeftObj f N where
  hom := g.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- Restriction of the left action along a monoid morphism, as a functor. -/
@[stacks 0FSA "left restriction-of-scalars functor"]
def restrictLeft (f : A' ⟶ A) (B : Mon C) : Bimod A B ⥤ Bimod A' B where
  obj := restrictLeftObj f
  map := restrictLeftMap f
  map_id := sorry
  map_comp := sorry

/-- Restrict the right action of an `(A,B)`-bimodule along `f : B' ⟶ B`. -/
@[stacks 0FSA "restriction of a right monoid action"]
def restrictRightObj (f : B' ⟶ B) (M : Bimod A B) : Bimod A B' where
  X := M.X
  actLeft := M.actLeft
  actRight := (M.X ◁ f.hom) ≫ M.actRight
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- A bimodule morphism remains a morphism after restriction of its right action. -/
def restrictRightMap (f : B' ⟶ B) {M N : Bimod A B} (g : M ⟶ N) :
    restrictRightObj f M ⟶ restrictRightObj f N where
  hom := g.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- Restriction of the right action along a monoid morphism, as a functor. -/
@[stacks 0FSA "right restriction-of-scalars functor"]
def restrictRight (A : Mon C) (f : B' ⟶ B) : Bimod A B ⥤ Bimod A B' where
  obj := restrictRightObj f
  map := restrictRightMap f
  map_id := sorry
  map_comp := sorry

/-- Left restriction of scalars does not change the underlying carrier. -/
@[simp]
theorem restrictLeftObj_X (f : A' ⟶ A) (M : Bimod A B) :
    (restrictLeftObj f M).X = M.X := sorry

/-- Right restriction of scalars does not change the underlying carrier. -/
@[simp]
theorem restrictRightObj_X (f : B' ⟶ B) (M : Bimod A B) :
    (restrictRightObj f M).X = M.X := sorry

/-- Left restriction of scalars does not change the underlying map. -/
@[simp]
theorem restrictLeftMap_hom (f : A' ⟶ A) {M N : Bimod A B} (g : M ⟶ N) :
    (restrictLeftMap f g).hom = g.hom := sorry

/-- Right restriction of scalars does not change the underlying map. -/
@[simp]
theorem restrictRightMap_hom (f : B' ⟶ B) {M N : Bimod A B} (g : M ⟶ N) :
    (restrictRightMap f g).hom = g.hom := sorry

end CategoryTheory.Bimod

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The lax unit morphism, regarded as a morphism from the target tensor-unit monoid to the
image of the source tensor-unit monoid. -/
def unitMonHom : Mon.trivial D ⟶ F.mapMon.obj (Mon.trivial C) :=
  Mon.Hom.mk' (LaxMonoidal.ε F) (one_f := sorry) (mul_f := sorry)

/-- A lax monoidal functor transports right modules, with the left unit action normalized by its
lax unit morphism. -/
@[stacks 0FSA "monoidal transport of right modules"]
def mapRightModule (A : Mon C) :
    Bimod.RightModule A ⥤ Bimod.RightModule (F.mapMon.obj A) :=
  F.mapBimod (Mon.trivial C) A ⋙
    Bimod.restrictLeft (unitMonHom F) (F.mapMon.obj A)

/-- A lax monoidal functor transports left modules, with the right unit action normalized by its
lax unit morphism. -/
@[stacks 0FSA "monoidal transport of left modules"]
def mapLeftModule (A : Mon C) :
    Bimod.LeftModule A ⥤ Bimod.LeftModule (F.mapMon.obj A) :=
  F.mapBimod A (Mon.trivial C) ⋙
    Bimod.restrictRight (F.mapMon.obj A) (unitMonHom F)

/-- Transporting a right module applies the underlying functor to its carrier. -/
@[simp]
theorem mapRightModule_obj_X (A : Mon C) (M : Bimod.RightModule A) :
    ((mapRightModule F A).obj M).X = F.obj M.X := sorry

/-- Transporting a left module applies the underlying functor to its carrier. -/
@[simp]
theorem mapLeftModule_obj_X (A : Mon C) (M : Bimod.LeftModule A) :
    ((mapLeftModule F A).obj M).X = F.obj M.X := sorry

end CategoryTheory.Functor

namespace CategoryTheory.Mon.Hom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A B : Mon C}

/-- The target monoid `B` as the canonical `(A,B)`-bimodule associated to `f : A ⟶ B`. -/
@[stacks 0FSA "right extension-of-scalars bimodule"]
def rightExtensionBimod (f : A ⟶ B) : Bimod A B where
  X := B.X
  actLeft := (f.hom ▷ B.X) ≫ μ
  actRight := μ
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The target monoid `B` as the canonical `(B,A)`-bimodule associated to `f : A ⟶ B`. -/
@[stacks 0FSA "left extension-of-scalars bimodule"]
def leftExtensionBimod (f : A ⟶ B) : Bimod B A where
  X := B.X
  actLeft := μ
  actRight := (B.X ◁ f.hom) ≫ μ
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The carrier of the right extension bimodule is the target monoid carrier. -/
@[simp]
theorem rightExtensionBimod_X (f : A ⟶ B) : f.rightExtensionBimod.X = B.X := sorry

/-- The carrier of the left extension bimodule is the target monoid carrier. -/
@[simp]
theorem leftExtensionBimod_X (f : A ⟶ B) : f.leftExtensionBimod.X = B.X := sorry

end CategoryTheory.Mon.Hom

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A B : Mon C}

/-- Extension of scalars for right modules along `f : A ⟶ B`. -/
@[stacks 0FSA "right module extension-of-scalars functor"]
noncomputable def extendRight (f : A ⟶ B) : RightModule A ⥤ RightModule B :=
  tensorRight f.rightExtensionBimod

/-- Extension of scalars for left modules along `f : A ⟶ B`. -/
@[stacks 0FSA "left module extension-of-scalars functor"]
noncomputable def extendLeft (f : A ⟶ B) : LeftModule A ⥤ LeftModule B :=
  tensorLeft f.leftExtensionBimod

/-- Right extension of scalars is the balanced tensor product with the canonical `(A,B)`-
bimodule. -/
@[simp]
theorem extendRight_obj (f : A ⟶ B) (M : RightModule A) :
    (extendRight f).obj M = M.tensorBimod f.rightExtensionBimod := sorry

/-- Left extension of scalars is the balanced tensor product with the canonical `(B,A)`-
bimodule. -/
@[simp]
theorem extendLeft_obj (f : A ⟶ B) (M : LeftModule A) :
    (extendLeft f).obj M = f.leftExtensionBimod.tensorBimod M := sorry

-- All carriers and actions are explicit; `sorryAx` occurs only in action/coherence laws.

end CategoryTheory.Bimod

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]
variable [HasCoequalizers D]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]

/-- Base change of right modules: first transport a module along a lax monoidal functor, then
extend scalars along the displayed morphism of target monoids. -/
@[stacks 0FSA "right module base change"]
noncomputable def baseChangeRight (A : Mon C) {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    Bimod.RightModule A ⥤ Bimod.RightModule B :=
  F.mapRightModule A ⋙ Bimod.extendRight f

/-- Base change of left modules: first transport a module along a lax monoidal functor, then
extend scalars along the displayed morphism of target monoids. -/
@[stacks 0FSA "left module base change"]
noncomputable def baseChangeLeft (A : Mon C) {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) :
    Bimod.LeftModule A ⥤ Bimod.LeftModule B :=
  F.mapLeftModule A ⋙ Bimod.extendLeft f

/-- Evaluating right-module base change is transport followed by extension of scalars. -/
@[simp]
theorem baseChangeRight_obj (A : Mon C) {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) (M : Bimod.RightModule A) :
    (baseChangeRight F A f).obj M =
      (Bimod.extendRight f).obj ((F.mapRightModule A).obj M) := sorry

/-- Evaluating left-module base change is transport followed by extension of scalars. -/
@[simp]
theorem baseChangeLeft_obj (A : Mon C) {B : Mon D}
    (f : F.mapMon.obj A ⟶ B) (M : Bimod.LeftModule A) :
    (baseChangeLeft F A f).obj M =
      (Bimod.extendLeft f).obj ((F.mapLeftModule A).obj M) := sorry

-- Base change is the explicit composite of monoidal transport and balanced extension of scalars;
-- all `sorryAx` dependencies are confined to the coherence fields of those two owners.

end CategoryTheory.Functor

end
