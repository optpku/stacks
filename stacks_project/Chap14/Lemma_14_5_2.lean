/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence
import StacksCheckRecall

/-!
@stack 016K
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/- Lemma 14.5.2: cosimplicial objects may equivalently be specified on the canonical
generators-and-relations presentation of the simplex category. -/
@[stacks 016K]
#check
  ((SimplexCategoryGenRel.Restriction.cosimplicial C).asEquivalence :
    CosimplicialObject C ≌ (SimplexCategoryGenRel ⥤ C))

#check CosimplicialObject.δ_naturality
#check CosimplicialObject.σ_naturality
#check CosimplicialObject.hom_ext
