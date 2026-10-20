/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tail Factorization of Functors

This file isolates the category-theoretic tail-factorization condition on a functor. No
filteredness, thinness, or algebraic structure on the target is needed for the core definition.
-/

open CategoryTheory

universe uI vI uC vC uD vD

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {C : Type uC} [Category.{vC} C]

/-- A functor has tail factorization if, from every source object, one arrow eventually factors
the image of every other arrow with that source. -/
@[stacks 059E "tail factorization"]
def HasTailFactorization (F : I ⥤ C) : Prop :=
  ∀ i, ∃ (j : I) (f : i ⟶ j),
    ∀ (k : I) (g : i ⟶ k), ∃ h : F.obj k ⟶ F.obj j, F.map f = F.map g ≫ h

/-- Tail factorization is preserved by postcomposition with any functor. -/
@[stacks 059E "postcomposition"]
theorem HasTailFactorization.map {D : Type uD} [Category.{vD} D]
    {F : I ⥤ C} (hF : F.HasTailFactorization) (G : C ⥤ D) :
    (F ⋙ G).HasTailFactorization := by
  intro i
  obtain ⟨j, f, hf⟩ := hF i
  refine ⟨j, f, fun k g ↦ ?_⟩
  obtain ⟨h, hh⟩ := hf k g
  refine ⟨G.map h, ?_⟩
  change G.map (F.map f) = G.map (F.map g) ≫ G.map h
  simpa using congrArg G.map hh

namespace FullyFaithful

/-- Postcomposition by a fully faithful functor preserves and reflects tail factorization. -/
@[stacks 059E "fully faithful invariance"]
theorem hasTailFactorization_iff {D : Type uD} [Category.{vD} D]
    {G : C ⥤ D} (hG : G.FullyFaithful) (F : I ⥤ C) :
    (F ⋙ G).HasTailFactorization ↔ F.HasTailFactorization := by
  constructor
  · intro hFG i
    obtain ⟨j, f, hf⟩ := hFG i
    refine ⟨j, f, fun k g ↦ ?_⟩
    obtain ⟨h, hh⟩ := hf k g
    refine ⟨hG.preimage h, ?_⟩
    apply hG.map_injective
    rw [G.map_comp, hG.map_preimage]
    exact hh
  · exact fun hF ↦ hF.map G

end FullyFaithful

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {I : Type uI} [Preorder I]
variable {C : Type uC} [Category.{vC} C]

/-- For a preorder-indexed functor, tail factorization can be written using eventual upper
bounds and the canonical morphisms supplied by inequalities. -/
@[stacks 059E "preorder criterion"]
theorem hasTailFactorization_iff_of_preorder (F : I ⥤ C) :
    F.HasTailFactorization ↔
      ∀ i, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  constructor
  · intro hF i
    obtain ⟨j, f, hf⟩ := hF i
    let hij : i ≤ j := leOfHom f
    refine ⟨j, hij, fun k hik ↦ ?_⟩
    obtain ⟨h, hh⟩ := hf k (homOfLE hik)
    refine ⟨h, ?_⟩
    simpa only [Subsingleton.elim f (homOfLE hij)] using hh
  · intro hF i
    obtain ⟨j, hij, hf⟩ := hF i
    refine ⟨j, homOfLE hij, fun k g ↦ ?_⟩
    obtain ⟨h, hh⟩ := hf k (leOfHom g)
    refine ⟨h, ?_⟩
    simpa only [Subsingleton.elim g (homOfLE (leOfHom g))] using hh

end CategoryTheory.Functor
