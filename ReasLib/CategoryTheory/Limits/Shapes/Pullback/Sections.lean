/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SplitEpi

variable {C : Type u} [Category.{v} C]

/-- The compatibility equality defining the section of the first projection of a pullback
induced by a chosen section of the second morphism. -/
theorem pullbackFst_fac {X Y Z : C} {g : Y ⟶ Z} (s : SplitEpi g) (f : X ⟶ Z) :
    𝟙 X ≫ f = (f ≫ s.section_) ≫ g := sorry

/-- A chosen section of `pullback.fst f g` induced by a chosen section of `g`. -/
def pullbackFst {X Y Z : C} {g : Y ⟶ Z} (s : SplitEpi g) (f : X ⟶ Z)
    [HasPullback f g] : SplitEpi (pullback.fst f g) where
  section_ := pullback.lift (𝟙 X) (f ≫ s.section_) (s.pullbackFst_fac f)
  id := sorry

/-- The section induced on the first pullback projection has the expected second
projection. -/
theorem pullbackFst_section_snd {X Y Z : C} {g : Y ⟶ Z} (s : SplitEpi g)
    (f : X ⟶ Z) [HasPullback f g] :
    (s.pullbackFst f).section_ ≫ pullback.snd f g = f ≫ s.section_ := sorry

/-- The compatibility equality defining the section of the second projection of a pullback
induced by a chosen section of the first morphism. -/
theorem pullbackSnd_fac {X Y Z : C} {f : X ⟶ Z} (s : SplitEpi f) (g : Y ⟶ Z) :
    (g ≫ s.section_) ≫ f = 𝟙 Y ≫ g := sorry

/-- A chosen section of `pullback.snd f g` induced by a chosen section of `f`. -/
def pullbackSnd {X Y Z : C} {f : X ⟶ Z} (s : SplitEpi f) (g : Y ⟶ Z)
    [HasPullback f g] : SplitEpi (pullback.snd f g) where
  section_ := pullback.lift (g ≫ s.section_) (𝟙 Y) (s.pullbackSnd_fac g)
  id := sorry

/-- The section induced on the second pullback projection has the expected first
projection. -/
theorem pullbackSnd_section_fst {X Y Z : C} {f : X ⟶ Z} (s : SplitEpi f)
    (g : Y ⟶ Z) [HasPullback f g] :
    (s.pullbackSnd g).section_ ≫ pullback.fst f g = g ≫ s.section_ := sorry

end CategoryTheory.SplitEpi
