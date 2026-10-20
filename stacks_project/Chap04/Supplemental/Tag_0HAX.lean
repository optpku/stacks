/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Unit.Unique
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory
open CategoryTheory.SemigroupalCategory

/- Lemma [Stacks 0HAX]
The multiplication identities, commutativity, conjugation formulas, and unique
multiplication-preserving comparison for arbitrary unit pairs. -/
@[stacks 0HAX] #check (CategoryTheory.SemigroupalCategory.UnitSeed.unit_unique :
  ∀ {C : Type u} [Category.{v} C] [SemigroupalCategory C] (seed : UnitSeed C),
    (whiskerRight seed.mul.hom seed.obj =
      (associator seed.obj seed.obj seed.obj).hom ≫ whiskerLeft seed.obj seed.mul.hom) ∧
    (∀ first second : End seed.obj, first * second = second * first) ∧
    (∀ endomorphism : seed.obj ⟶ seed.obj,
      endomorphism = seed.mul.inv ≫ whiskerRight endomorphism seed.obj ≫ seed.mul.hom ∧
      endomorphism = seed.mul.inv ≫ whiskerLeft seed.obj endomorphism ≫ seed.mul.hom) ∧
    (∀ second : UnitSeed C, ∃! comparison : second.obj ≅ seed.obj,
      tensorHom comparison.hom comparison.hom ≫ seed.mul.hom =
        second.mul.hom ≫ comparison.hom))
