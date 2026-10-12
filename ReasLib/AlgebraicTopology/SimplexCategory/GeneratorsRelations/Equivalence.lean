/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0168

# The generators-and-relations presentation of the simplex category

The canonical functor from `SimplexCategoryGenRel` to `SimplexCategory` is an equivalence.
Keeping this instance with the indexing category makes the induced equivalences on simplicial
and cosimplicial functor categories available without importing a source chapter.
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategoryGenRel

universe v u

/-- The canonical generators-and-relations presentation of the simplex category is equivalent to
`SimplexCategory`. -/
@[stacks 0168, instance]
theorem toSimplexCategory.isEquivalence : toSimplexCategory.IsEquivalence := sorry

namespace Restriction

variable (C : Type u) [Category.{v} C]

/-- Restriction of simplicial objects to the opposite generators-and-relations presentation. -/
@[stacks 016B "simplicial restriction to the generators-and-relations presentation"]
abbrev simplicial :
    SimplicialObject C ⥤ (SimplexCategoryGenRelᵒᵖ ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj toSimplexCategory.op

/-- Restriction of cosimplicial objects to the generators-and-relations presentation. -/
@[stacks 016K "cosimplicial restriction to the generators-and-relations presentation"]
abbrev cosimplicial :
    CosimplicialObject C ⥤ (SimplexCategoryGenRel ⥤ C) :=
  (Functor.whiskeringLeft _ _ C).obj toSimplexCategory

/-- The generic equivalence instance for left whiskering, specialized across the cosimplicial
abbreviation so that typeclass search does not depend on unfolding that abbreviation. -/
@[stacks 016K "cosimplicial restriction equivalence"]
instance cosimplicial.isEquivalence : (cosimplicial C).IsEquivalence :=
  Functor.instIsEquivalenceObjWhiskeringLeft toSimplexCategory

end Restriction

section RestrictionChecks

variable (C : Type u) [Category.{v} C]

#synth (Restriction.simplicial C).IsEquivalence
#synth (Restriction.cosimplicial C).IsEquivalence

end RestrictionChecks

end SimplexCategoryGenRel
