/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monotonicity of Localizers on Full Subcategories

An inclusion of object properties induces a localizer morphism between the corresponding
restricted systems.  A simultaneous inclusion of denominator systems is obtained by first
weakening the denominator and then enlarging the full subcategory.
-/

@[expose] public section

universe v u

namespace CategoryTheory.fullSubcategoryLocalizerMorphism

open MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  {P Q : ObjectProperty D} {S T : MorphismProperty D}

/-- Enlarge the object property while keeping the ambient denominator system fixed.  This
localizer morphism is induced by the full-subcategory inclusion. -/
@[stacks 0GSL "monotonicity of localized full subcategories"]
abbrev ofLE (S : MorphismProperty D) (hP : P ≤ Q) :
    LocalizerMorphism (fullSubcategoryLocalizationSystem P S)
      (fullSubcategoryLocalizationSystem Q S) :=
  LocalizerMorphism.ofEq (F := P.ιOfLE hP) rfl

/-- Simultaneously enlarge the object property and the ambient denominator system. -/
@[stacks 0GSL "two-variable monotonicity of localized full subcategories"]
abbrev mapOfLE (hP : P ≤ Q) (hS : S ≤ T) :
    LocalizerMorphism (fullSubcategoryLocalizationSystem P S)
      (fullSubcategoryLocalizationSystem Q T) :=
  (LocalizerMorphism.ofLE (MorphismProperty.monotone_inverseImage P.ι hS)).comp
    (ofLE T hP)

namespace mapOfLE

/-- The two-variable monotonicity localizer maps an object along `ObjectProperty.ιOfLE`. -/
@[simp]
theorem functor_obj (hP : P ≤ Q) (hS : S ≤ T) (X : P.FullSubcategory) :
    (mapOfLE hP hS).functor.obj X = (P.ιOfLE hP).obj X := sorry

/-- The two-variable monotonicity localizer maps a morphism along
`ObjectProperty.ιOfLE`. -/
@[simp]
theorem functor_map (hP : P ≤ Q) (hS : S ≤ T)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    (mapOfLE hP hS).functor.map f = (P.ιOfLE hP).map f := sorry

/-- Reflexive two-variable monotonicity is the identity localizer morphism. -/
theorem refl :
    mapOfLE (P := P) (Q := P) (S := S) (T := S) le_rfl le_rfl =
      LocalizerMorphism.id (fullSubcategoryLocalizationSystem P S) := sorry

/-- Successive two-variable inclusions agree with the inclusion defined by the composite
inequalities. -/
theorem trans {R : ObjectProperty D} {U : MorphismProperty D}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) (hST : S ≤ T) (hTU : T ≤ U) :
    (mapOfLE hPQ hST).comp (mapOfLE hQR hTU) =
      mapOfLE (hPQ.trans hQR) (hST.trans hTU) := sorry

end mapOfLE

end CategoryTheory.fullSubcategoryLocalizerMorphism
