/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Identity.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.Composition.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict-pseudofunctor computations for based inertia

This leaf exposes the object, local-functor, `1`-cell, `2`-cell, and comparison projections of
the strict based-inertia pseudofunctor.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂' u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section InertiaPseudofunctor

open Bicategory
open scoped Bicategory

namespace Inertia

namespace strictPseudofunctor

/-- The pseudofunctor underlying the strict based-inertia pseudofunctor is `pseudofunctor`. -/
@[simp, stacks 04Z4 "strict based inertia ordinary-pseudofunctor view"]
theorem toPseudofunctor :
    (strictPseudofunctor C).toPseudofunctor =
      pseudofunctor C := sorry

/-- The strict based-inertia pseudofunctor sends an object to its inertia category. -/
@[simp, stacks 04Z4 "strict based inertia object computation"]
theorem obj (X : BasedCategory.{v₁, u₁} C) :
    (strictPseudofunctor C).obj X = inertia X := sorry

/-- The strict local action is the public inertia hom functor. -/
@[simp, stacks 04Z4 "strict based inertia hom-functor computation"]
theorem mapFunctor
    (X Y : BasedCategory.{v₁, u₁} C) :
    (strictPseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The strict `1`-cell action is the canonical inertia map. -/
@[simp, stacks 04Z4 "strict based inertia map computation"]
theorem map
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    (strictPseudofunctor C).map F = Inertia.map F := sorry

/-- Strict based inertia preserves identity `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "strict based inertia identity law"]
theorem map_id (X : BasedCategory.{v₁, u₁} C) :
    (strictPseudofunctor C).map (𝟭 X) =
      𝟭 ((strictPseudofunctor C).obj X) := sorry

/-- Strict based inertia preserves composition of `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "strict based inertia composition law"]
theorem map_comp
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    (strictPseudofunctor C).map (F ⋙ G) =
      (strictPseudofunctor C).map F ⋙
        (strictPseudofunctor C).map G := sorry

/-- The strict `2`-cell action is the canonical inertia `2`-cell. -/
@[simp, stacks 04Z4 "strict based inertia two-cell computation"]
theorem map₂
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    (strictPseudofunctor C).map₂ η = Inertia.map₂ η := sorry

/-- The strict identity comparison is the explicit componentwise inertia comparison. -/
@[simp, stacks 04Z4 "strict based inertia identity comparison"]
theorem mapId (X : BasedCategory.{v₁, u₁} C) :
    (strictPseudofunctor C).mapId X = Inertia.mapIdIso X := sorry

/-- The strict composition comparison is the explicit componentwise inertia comparison. -/
@[simp, stacks 04Z4 "strict based inertia composition comparison"]
theorem mapComp
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    (strictPseudofunctor C).mapComp F G =
      Inertia.mapCompIso F G := sorry

end strictPseudofunctor

end Inertia
end InertiaPseudofunctor

end BasedCategory
end CategoryTheory
