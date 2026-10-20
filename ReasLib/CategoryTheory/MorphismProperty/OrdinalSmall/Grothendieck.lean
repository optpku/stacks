/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import ReasLib.CategoryTheory.MorphismProperty.OrdinalSmall

/-!
# Ordinal-small objects in Grothendieck abelian categories

This file relates the cardinality of the subobject lattice of an object to its ordinal
smallness relative to monomorphisms. The canonical statement uses `HasCardinalLT`, so the
Grothendieck and ordinal universes need not be tied to the object universe.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.MorphismProperty.IsOrdinalSmall

/-- In a Grothendieck abelian category, an object is ordinal-small relative to monomorphisms
whenever its subobject lattice is smaller than the cofinality of the indexing ordinal. -/
@[stacks 079F "HasCardinalLT form"]
theorem monomorphisms_of_hasCardinalLT_cof
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (M : C) (α : Ordinal.{w}) (hM : HasCardinalLT (Subobject M) α.cof) :
    (monomorphisms C).IsOrdinalSmall M α := sorry

/-- Proposition 19.11.5: if the cardinality of the subobject lattice of `M` is smaller than
`α.cof`, then `M` is `α`-small relative to monomorphisms. -/
@[stacks 079F "subobject-cardinality form"]
theorem monomorphisms_of_cardinalMk_lt_cof
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (M : C) (α : Ordinal.{max u v})
    (hM : Cardinal.mk (Subobject M) < α.cof) :
    (monomorphisms C).IsOrdinalSmall M α := sorry

end CategoryTheory.MorphismProperty.IsOrdinalSmall
