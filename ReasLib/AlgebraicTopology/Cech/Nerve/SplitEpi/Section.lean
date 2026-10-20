/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.Projection
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sections of split Čech nerves

This module owns the functorial Čech-nerve section associated to a bundled split
epimorphism.  An explicit section and its identity enter this API through `SplitEpi.mk`.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f : X ⟶ Y}
variable [(Arrow.mk f).HasCechNerve]

namespace SplitEpi

namespace cechNerve

namespace sectionEndomorphism

/-- The chosen section square commutes with the split epimorphism. -/
@[stacks 019P "split Čech-nerve section square"]
theorem arrowHom.w (S : SplitEpi f) :
    (f ≫ S.section_) ≫ f = f ≫ 𝟙 Y := sorry

/-- The arrow endomorphism induced by the chosen section of a split epimorphism. -/
@[stacks 019P "split Čech-nerve section arrow endomorphism"]
def arrowHom (S : SplitEpi f) :
    Arrow.mk f ⟶ Arrow.mk f :=
  Arrow.homMk (f ≫ S.section_) (𝟙 Y) (arrowHom.w S)

/-- The Čech-nerve endomorphism induced by a chosen split epimorphism. -/
@[stacks 019P "split Čech-nerve section endomorphism"]
def map (S : SplitEpi f) :
    (Arrow.mk f).cechNerve ⟶ (Arrow.mk f).cechNerve :=
  Arrow.mapCechNerve (arrowHom S)

/-- Each vertex of the section-induced Čech-nerve endomorphism is obtained by composing the
corresponding wide-pullback projection with the split epimorphism and its chosen section. -/
@[reassoc (attr := simp), stacks 019P "split Čech-nerve section endomorphism projection"]
theorem map.app_π (S : SplitEpi f) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    (map S).app n ≫ Arrow.cechNerve.π (Arrow.mk f) n i =
      Arrow.cechNerve.π (Arrow.mk f) n i ≫ f ≫ S.section_ := sorry

end sectionEndomorphism

namespace sectionMap

/-- The degreewise diagonal section from the target of a split epimorphism to its Čech nerve. -/
@[stacks 019P "degreewise split Čech-nerve section"]
def app (S : SplitEpi f) (n : SimplexCategoryᵒᵖ) :
    Y ⟶ (Arrow.mk f).cechNerve.obj n :=
  Arrow.cechNerve.lift (Arrow.mk f) n (𝟙 Y)
    (fun _ : Fin (n.unop.len + 1) ↦ S.section_) (fun _ ↦ S.id)

/-- The degreewise Čech-nerve section maps to the target by the identity. -/
@[reassoc (attr := simp), stacks 019P "split Čech-nerve section on the base"]
theorem app_base (S : SplitEpi f) (n : SimplexCategoryᵒᵖ) :
    app S n ≫ Arrow.cechNerve.base (Arrow.mk f) n = 𝟙 Y := sorry

/-- The degreewise Čech-nerve section has the chosen split section in every vertex coordinate. -/
@[reassoc (attr := simp), stacks 019P "split Čech-nerve section on vertices"]
theorem app_π (S : SplitEpi f) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    app S n ≫ Arrow.cechNerve.π (Arrow.mk f) n i = S.section_ := sorry

/-- The degreewise Čech-nerve sections of a split epimorphism commute with simplex operators. -/
@[stacks 019P "split Čech-nerve section naturality"]
theorem naturality (S : SplitEpi f)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    ((SimplicialObject.const C).obj Y).map α ≫ app S m =
      app S n ≫ (Arrow.mk f).cechNerve.map α := sorry

/-- The target of a split epimorphism embeds as the diagonal constant simplicial object in its
Čech nerve. -/
@[stacks 019P "split Čech-nerve section"]
def hom (S : SplitEpi f) :
    (SimplicialObject.const C).obj Y ⟶ (Arrow.mk f).cechNerve :=
  { app := app S
    naturality := fun _ _ α ↦ naturality S α }

/-- The component of the canonical Čech-nerve section is the degreewise diagonal section. -/
@[simp, stacks 019P "split Čech-nerve section component"]
theorem hom.app (S : SplitEpi f) (n : SimplexCategoryᵒᵖ) :
    (hom S).app n = app S n := sorry

/-- The canonical diagonal section agrees with the section supplied by the standard extra
degeneracy on the augmented Čech nerve. -/
@[stacks 019P "split Čech-nerve section extra-degeneracy bridge"]
theorem hom.eq_extraDegeneracy (S : SplitEpi f) :
    hom S =
      (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk f) S).section_ := sorry

/-- The diagonal section is compatible with the constant and Čech-nerve augmentations. -/
@[stacks 019P "split Čech-nerve section augmentation compatibility"]
theorem augmented.w (S : SplitEpi f) :
    hom S ≫ (Arrow.mk f).augmentedCechNerve.hom =
      ((SimplicialObject.Augmented.const).obj Y).hom ≫
        (SimplicialObject.const C).map (𝟙 Y) := sorry

/-- The augmented Čech-nerve section associated to a chosen split epimorphism. -/
@[stacks 019P "augmented split Čech-nerve section"]
def augmented (S : SplitEpi f) :
    (SimplicialObject.Augmented.const).obj Y ⟶ (Arrow.mk f).augmentedCechNerve where
  left := hom S
  right := 𝟙 Y
  w := augmented.w S

/-- The Čech-nerve section is a right inverse to the augmentation. -/
@[reassoc (attr := simp), stacks 019P "split Čech-nerve section augmentation identity"]
theorem comp_augmentation (S : SplitEpi f) :
    hom S ≫ (Arrow.mk f).augmentedCechNerve.hom =
      𝟙 ((SimplicialObject.const C).obj Y) := sorry

end sectionMap

namespace augmentation

/-- Composing the Čech-nerve augmentation with its section yields the endomorphism induced by
the chosen split epimorphism. -/
@[reassoc (attr := simp), stacks 019P "split Čech-nerve augmentation section identity"]
theorem comp_section (S : SplitEpi f) :
    (Arrow.mk f).augmentedCechNerve.hom ≫ sectionMap.hom (f := f) S =
      sectionEndomorphism.map (f := f) S := sorry

end augmentation

end cechNerve

end SplitEpi

end CategoryTheory
