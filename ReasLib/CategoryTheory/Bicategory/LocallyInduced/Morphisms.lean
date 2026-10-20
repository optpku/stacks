/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphism constructors and extensionality for locally induced bicategories

This leaf owns the small constructor and extensionality API for selected 1-morphisms, ambient
2-morphisms, and their 2-isomorphisms. It keeps downstream code independent of the
full-subcategory implementation used by the bicategory construction.
-/

@[expose] public section

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

universe w v u u'

variable {B : Type u'}
variable {C : Type u} [Bicategory.{w, v} C]
variable {F : B → C} {Q : HomProperty F} [Q.IsMultiplicative]

/-- Build a 2-morphism from its ambient representative. -/
abbrev mkHom₂ {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (η : f.obj ⟶ g.obj) : f ⟶ g :=
  ObjectProperty.homMk η

/-- The ambient representative of a mkHom₂ cell is the supplied cell. -/
@[simp]
theorem mkHom₂.toAmbient {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (η : f.obj ⟶ g.obj) :
    (mkHom₂ η).hom = η := sorry

/-- Equality of selected 1-morphisms is detected by their ambient representatives. -/
@[ext]
theorem hom_ext {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    (h : f.obj = g.obj) : f = g := sorry

/-- Equality of selected 2-morphisms is detected by their ambient representatives. -/
@[ext]
theorem hom₂_ext {X Y : LocallyInducedBicategory C F Q} {f g : X ⟶ Y}
    {η θ : f ⟶ g} (h : η.hom = θ.hom) : η = θ := sorry

end CategoryTheory.Bicategory.LocallyInducedBicategory
