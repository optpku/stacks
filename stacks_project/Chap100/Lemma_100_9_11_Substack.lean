/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.Factorization

/-!
# Bicategorical factorization

The generic factorization predicate and its existential specification are
available from their mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.FactorsThrough :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}, (Y ⟶ X) → (Z ⟶ X) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.factorsThrough_iff :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : Y ⟶ X) (ι : Z ⟶ X),
    AlgebraicGeometry.Groupoids.Hom.FactorsThrough f ι ↔
      ∃ g : Y ⟶ Z, Nonempty (g ≫ ι ≅ f))
