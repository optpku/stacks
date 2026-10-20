/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.Strict
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Embeddings into Finite Filtered-Injective Objects

A strict filtered-injective embedding packages the target and morphism separately from the
existence theorem. This is the reusable input expected by resolution and derived-functor
constructions.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

/-- A strict monomorphism from a finite filtered object into a finite filtered-injective object. -/
@[stacks 05TS "strict filtered-injective embedding"]
structure Embedding (A : FilteredObject.Finite.category C) where
  /-- The finite filtered-injective target. -/
  target : category C
  /-- The embedding into the underlying finite filtered object of `target`. -/
  hom : A ⟶ target.obj
  /-- The underlying ambient morphism is a monomorphism. -/
  mono : Mono hom.hom.hom
  /-- The underlying morphism of filtered objects is strict. -/
  strict : FilteredObject.Hom.Strict hom.hom

namespace Embedding

/-- The ambient morphism underlying a strict filtered-injective embedding. -/
def underlying {A : FilteredObject.Finite.category C} (e : Embedding A) :
    A.obj.obj ⟶ e.target.obj.obj.obj := e.hom.hom.hom

/-- Over an abelian category with enough injectives, every finite filtered object admits a strict
filtered-injective embedding. -/
@[stacks 05TS]
theorem nonempty [EnoughInjectives C] (A : FilteredObject.Finite.category C) :
    Nonempty (Embedding A) := sorry

/-- Existential form of a strict filtered-injective embedding, matching the individual target,
morphism, monomorphism, and strictness clauses. -/
theorem nonempty_iff (A : FilteredObject.Finite.category C) :
    Nonempty (Embedding A) ↔
      ∃ (I : category C) (f : A ⟶ I.obj),
        Mono f.hom.hom ∧ FilteredObject.Hom.Strict f.hom := sorry

end Embedding

end CategoryTheory.FilteredObject.Finite.FilteredInjective
