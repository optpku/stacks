/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Extensionality
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Characterizing Triangulated Localizations

This file removes two pieces of proof-local setup from downstream uses of a
triangulated localization. First, the calculus of fractions supplies the
essential surjectivity on arrows needed to recognize distinguished triangles.
Second, exactness of the localization functor uniquely determines the target
pretriangulated structure once the additive and shift data are fixed.
-/

open CategoryTheory Limits Pretriangulated Localization

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor.IsLocalization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ]

/-- A localization admitting left fractions recognizes distinguished triangles as the essential
image of the distinguished triangles in its source. The required essential surjectivity of the
map on arrows is derived from the localization API rather than exposed as a caller-supplied
instance. -/
@[stacks 05R6 "distinguished triangles in a triangulated localization"]
theorem distTriang_iff
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [L.CommShift ℤ]
    [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [L.IsTriangulated] (T : Triangle D) :
    T ∈ distTriang D ↔ T ∈ L.essImageDistTriang := sorry

/-- A localization admitting right fractions also recognizes distinguished triangles as the
essential image of the distinguished triangles in its source. -/
theorem distTriang_iff_of_hasRightCalculus
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] [L.CommShift ℤ]
    [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [L.IsTriangulated] (T : Triangle D) :
    T ∈ distTriang D ↔ T ∈ L.essImageDistTriang := sorry

/-- For an explicit pretriangulated target structure making a localization exact, its
distinguished triangles are exactly the essential image of the source distinguished triangles. -/
theorem distinguishedTriangles_eq_essImage
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [L.CommShift ℤ]
    [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (P : Pretriangulated D)
    (hP : ∀ (T : Triangle C), T ∈ distTriang C →
      L.mapTriangle.obj T ∈ P.distinguishedTriangles) :
    P.distinguishedTriangles = L.essImageDistTriang := sorry

end Functor.IsLocalization

namespace Triangulated.Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ]

/-- With the additive, shift, and shift-comparison data fixed, exactness of a localization functor
determines the pretriangulated structure on its target. The target structure is an explicit
parameter, so callers do not need a temporary local instance to state or use the uniqueness
property. -/
@[stacks 05R6 "uniqueness of the pretriangulated localization"]
theorem pretriangulated_eq_of_map_distinguished
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [W.IsCompatibleWithTriangulation]
    [L.CommShift ℤ]
    [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [L.Additive]
    (P : Pretriangulated D)
    (hP : ∀ (T : Triangle C), T ∈ distTriang C →
      L.mapTriangle.obj T ∈ P.distinguishedTriangles) :
    P = pretriangulated L W := sorry

/-- With the additive, shift, and shift-comparison data fixed, any localization model admitting
left fractions has a unique target pretriangulated structure that makes the localization functor
exact. -/
@[stacks 05R6 "model-independent uniqueness of the pretriangulated localization"]
theorem existsUniquePretriangulated
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [W.IsCompatibleWithTriangulation]
    [L.CommShift ℤ] [HasZeroObject D] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [L.Additive] :
    ∃! P : Pretriangulated D,
      ∀ (T : Triangle C), T ∈ distTriang C →
        L.mapTriangle.obj T ∈ P.distinguishedTriangles := sorry

end Triangulated.Localization

namespace MorphismProperty.Localization

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Distinguished triangles in the canonical localization are exactly the essential image of
distinguished triangles in the source. -/
@[stacks 05R6 "canonical distinguished triangles in a triangulated localization"]
theorem distTriang_iff
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.IsCompatibleWithTriangulation] (T : Triangle W.Localization) :
    T ∈ distTriang W.Localization ↔ T ∈ W.Q.essImageDistTriang := sorry

/-- Stacks 05R6: if a triangulation-compatible morphism property admits both fraction calculi,
then, after fixing the canonical additive, shift, and shift-comparison data on its localization,
there is a unique pretriangulated structure for which the localization functor maps distinguished
triangles to distinguished triangles. -/
@[stacks 05R6 "existence and uniqueness of the pretriangulated localization"]
theorem existsUniquePretriangulated
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    [W.HasRightCalculusOfFractions] [W.IsCompatibleWithTriangulation] :
    ∃! P : Pretriangulated W.Localization,
      ∀ (T : Triangle C), T ∈ distTriang C →
        W.Q.mapTriangle.obj T ∈ P.distinguishedTriangles := sorry

end MorphismProperty.Localization

end CategoryTheory
