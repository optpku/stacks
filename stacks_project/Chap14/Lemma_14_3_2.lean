/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence
import StacksCheckRecall

/-!
@stack 016B
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/- Lemma 14.3.2: simplicial objects may equivalently be specified on the canonical
generators-and-relations presentation of the simplex category. -/
@[stacks 016B]
#check
  ((SimplexCategoryGenRel.Restriction.simplicial C).asEquivalence :
    SimplicialObject C ≌ (SimplexCategoryGenRelᵒᵖ ⥤ C))

#check SimplicialObject.δ_naturality
#check SimplicialObject.σ_naturality
#check SimplicialObject.hom_ext
