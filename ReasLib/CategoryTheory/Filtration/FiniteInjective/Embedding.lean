/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.Strict
public import ReasLib.CategoryTheory.Filtration.Functors
public import ReasLib.CategoryTheory.Filtration.IntervalSplit.Injective
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Embeddings into Finite Filtered-Injective Objects

A strict filtered-injective embedding packages the target and morphism separately from the
existence theorem. This is the reusable input expected by resolution and derived-functor
constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

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

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The ambient morphism underlying a strict filtered-injective embedding. -/
def underlying {A : FilteredObject.Finite.category C} (e : Embedding A) :
    A.obj.obj ⟶ e.target.obj.obj.obj := e.hom.hom.hom

/-- The only object choices in the embedding are ambient injective presentations of the
quotients `A / F^(i+1) A`. No filtered existence theorem is used. -/
def quotientPresentation [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ)
    (i : Set.Icc a b) : InjectivePresentation (A.quotient (i.1 + 1)) :=
  Classical.choice (EnoughInjectives.presentation (A.quotient (i.1 + 1)))

/-- The interval-split target of 05TS, before imposing any bounds on the source filtration.
Keeping the interval explicit lets iterated cokernels reuse the original bounds. -/
def targetAtBounds [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) : category C :=
  ⟨FilteredObject.IntervalSplit.filteredObject a b
      (fun i ↦ (quotientPresentation A a b i).J),
    FilteredObject.IntervalSplit.FilteredInjective.of_components a b _
      (fun i ↦ (quotientPresentation A a b i).injective)⟩

/-- The ambient diagonal of quotient projections followed by the chosen injective embeddings. -/
def diagonal [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    A.obj ⟶ (targetAtBounds A a b).obj.obj.obj :=
  biproduct.lift fun i ↦
    cokernel.π (A.filtration.stage (i.1 + 1)).arrow ≫ (quotientPresentation A a b i).f

/-- The component formula specifies the actual map in 05TS. -/
@[simp]
theorem diagonal_π [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ)
    (i : Set.Icc a b) :
    diagonal A a b ≫ biproduct.π (fun j ↦ (quotientPresentation A a b j).J) i =
      cokernel.π (A.filtration.stage (i.1 + 1)).arrow ≫
        (quotientPresentation A a b i).f :=
  biproduct.lift_π _ _

/-- Components below `p` vanish on `F^p A`, so the diagonal preserves the tail filtration. -/
theorem diagonal_preserves [EnoughInjectives C] (A : FilteredObject C) (a b p : ℤ) :
    ((targetAtBounds A a b).obj.obj.filtration.stage p).Factors
      ((A.filtration.stage p).arrow ≫ diagonal A a b) := sorry

/-- The diagonal as a filtered morphism. Its data do not depend on filtration-bound proofs. -/
def inclusionAtBounds [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ) :
    A ⟶ (targetAtBounds A a b).obj.obj :=
  FilteredObject.Hom.mk (diagonal A a b) (diagonal_preserves A a b)

/-- The rightmost quotient detects monicity when the next source stage is zero. -/
theorem diagonal_mono [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ)
    (hab : a ≤ b) (hb : A.filtration.stage (b + 1) = ⊥) :
    Mono (diagonal A a b) := sorry

/-- The diagonal is strict when the interval contains the source filtration. -/
theorem inclusionAtBounds_strict [EnoughInjectives C] (A : FilteredObject C) (a b : ℤ)
    (hab : a ≤ b) (ha : A.filtration.stage a = ⊤)
    (hb : A.filtration.stage (b + 1) = ⊥) :
    FilteredObject.Hom.Strict (inclusionAtBounds A a b) := sorry

/-- The strict embedding of 05TS at specified filtration bounds. Only its law fields use
the bounds; the target and map are the explicit finite direct sum and diagonal. -/
@[stacks 05TS "strict embedding at explicit filtration bounds"]
def ofBounds [EnoughInjectives C] (A : FilteredObject.Finite.category C) (a b : ℤ)
    (hab : a ≤ b) (ha : A.obj.filtration.stage a = ⊤)
    (hb : A.obj.filtration.stage (b + 1) = ⊥) : Embedding A where
  target := targetAtBounds A.obj a b
  hom := ⟨inclusionAtBounds A.obj a b⟩
  mono := diagonal_mono A.obj a b hab hb
  strict := inclusionAtBounds_strict A.obj a b hab ha hb

/-- A zero-stage bound selected directly from the input finite filtration. -/
def upperBound (A : FilteredObject.Finite.category C) : ℤ :=
  Classical.choose (Classical.choose_spec A.property)

/-- A top-stage bound no greater than the chosen zero-stage bound. These are choices from
the supplied object's finite-filtration certificate, not from a derived existence theorem. -/
def lowerBound (A : FilteredObject.Finite.category C) : ℤ :=
  min (Classical.choose A.property) (upperBound A)

theorem lowerBound_le_upperBound (A : FilteredObject.Finite.category C) :
    lowerBound A ≤ upperBound A := min_le_right _ _

theorem stage_lowerBound (A : FilteredObject.Finite.category C) :
    A.obj.filtration.stage (lowerBound A) = ⊤ := by
  apply le_antisymm le_top
  rw [← (Classical.choose_spec (Classical.choose_spec A.property)).1]
  exact A.obj.filtration.stage_mono (min_le_left _ _)

theorem stage_upperBound_succ (A : FilteredObject.Finite.category C) :
    A.obj.filtration.stage (upperBound A + 1) = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← (Classical.choose_spec (Classical.choose_spec A.property)).2]
  exact A.obj.filtration.stage_mono (show upperBound A ≤ upperBound A + 1 by omega)

/-- Construct the strict filtered-injective embedding using the given `EnoughInjectives`.
The only choices are the input filtration bounds and ambient injective presentations. -/
@[stacks 05TS "explicit strict filtered-injective embedding"]
def ofEnoughInjectives [EnoughInjectives C] (A : FilteredObject.Finite.category C) :
    Embedding A :=
  ofBounds A (lowerBound A) (upperBound A) (lowerBound_le_upperBound A)
    (stage_lowerBound A) (stage_upperBound_succ A)

/-- Over an abelian category with enough injectives, every finite filtered object admits a strict
filtered-injective embedding. -/
@[stacks 05TS]
theorem nonempty [EnoughInjectives C] (A : FilteredObject.Finite.category C) :
    Nonempty (Embedding A) := ⟨ofEnoughInjectives A⟩

/-- Existential form of a strict filtered-injective embedding, matching the individual target,
morphism, monomorphism, and strictness clauses. -/
theorem nonempty_iff (A : FilteredObject.Finite.category C) :
    Nonempty (Embedding A) ↔
      ∃ (I : category C) (f : A ⟶ I.obj),
        Mono f.hom.hom ∧ FilteredObject.Hom.Strict f.hom := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.target, e.hom, e.mono, e.strict⟩
  · rintro ⟨I, f, hm, hs⟩
    exact ⟨⟨I, f, hm, hs⟩⟩

end Embedding

end CategoryTheory.FilteredObject.Finite.FilteredInjective
