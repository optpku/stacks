/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Reindex.Explicit.Naturality
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso

/-!
# Coherence for explicit categorical-pullback reindexing

This leaf records the identity and composition boundaries for the explicit
reindexing comparison. The concrete construction is owned by
`Explicit.Construction`; naturality and conjugation formulas are owned by
`Explicit.Naturality`.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor

namespace Limits.CategoricalPullback.Reindex.explicit

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Identity coherence for the pullback-fiber reindexing comparison.  The comparison along
`𝟙 U`, the source unit comparison, transport along `u.map_id`, and the target unit comparison
form the expected commutative boundary. -/
theorem comparisonNatIso.id.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    (U : C) (X : (π₁ u p).Fiber U) :
    (Fiber.forward.functor u p χ U).map
          (Cleavage.Reindex.idIsoApp (χ.ofRight u) U X).hom ≫
        (comparisonIso u p χ (𝟙 U) X).hom ≫
        (Cleavage.Reindex.congrIsoApp χ (u.map_id U)
          ((Fiber.forward.functor u p χ U).obj X)).hom =
      (Cleavage.Reindex.idIsoApp χ (u.obj U)
        ((Fiber.forward.functor u p χ U).obj X)).hom := sorry

/-- Inverse identity coherence for the pullback-fiber reindexing comparison. -/
theorem comparisonNatIso.id.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    (U : C) (X : (π₁ u p).Fiber U) :
    (Cleavage.Reindex.idIsoApp χ (u.obj U)
          ((Fiber.forward.functor u p χ U).obj X)).inv =
      (Cleavage.Reindex.congrIsoApp χ (u.map_id U)
          ((Fiber.forward.functor u p χ U).obj X)).inv ≫
        (comparisonIso u p χ (𝟙 U) X).inv ≫
        (Fiber.forward.functor u p χ U).map
          (Cleavage.Reindex.idIsoApp (χ.ofRight u) U X).inv := sorry

/-- Composition coherence for the pullback-fiber reindexing comparison.  Direct comparison
along `b ≫ a` agrees with successive comparison along `a` and `b`, with the target functor's
`u.map_comp` transport recorded by the specified-composite reindexing comparison. -/
theorem comparisonNatIso.comp.hom
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (comparisonIso u p χ (b ≫ a) X).hom ≫
        (Cleavage.Reindex.specifiedCompIsoApp χ (u.map a) (u.map b) (u.map (b ≫ a))
          (u.map_comp b a).symm
          ((Fiber.forward.functor u p χ U).obj X)).hom =
      (Fiber.forward.functor u p χ W).map
          (Cleavage.Reindex.compIsoApp (χ.ofRight u) a b X).hom ≫
        (comparisonIso u p χ b
          ((χ.ofRight u).reindexObj a X)).hom ≫
        (χ.reindex (u.map b)).map
          (comparisonIso u p χ a X).hom := sorry

/-- Inverse composition coherence for the pullback-fiber reindexing comparison. -/
theorem comparisonNatIso.comp.inv
    (u : C ⥤ D) (p : S ⥤ D) (χ : p.Cleavage)
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V)
    (X : (π₁ u p).Fiber U) :
    (Cleavage.Reindex.specifiedCompIsoApp χ (u.map a) (u.map b) (u.map (b ≫ a))
          (u.map_comp b a).symm
          ((Fiber.forward.functor u p χ U).obj X)).inv ≫
        (comparisonIso u p χ (b ≫ a) X).inv =
      (χ.reindex (u.map b)).map
          (comparisonIso u p χ a X).inv ≫
        (comparisonIso u p χ b
          ((χ.ofRight u).reindexObj a X)).inv ≫
        (Fiber.forward.functor u p χ W).map
          (Cleavage.Reindex.compIsoApp (χ.ofRight u) a b X).inv := sorry

end Limits.CategoricalPullback.Reindex.explicit

end CategoryTheory
