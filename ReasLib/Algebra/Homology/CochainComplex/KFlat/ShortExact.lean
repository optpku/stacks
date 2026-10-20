/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complexes in short exact sequences

@stack 0BYH

For a short exact sequence of cochain complexes of modules whose right term is termwise flat,
K-flatness satisfies two-out-of-three.  The three implications are exposed separately so that
consumers can use exactly the pair of hypotheses available to them.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}

/-- Lemma 15.59.6 (1): if the right term is termwise flat and the first two terms of a short
exact sequence are K-flat, then the right term is K-flat. -/
@[stacks 0BYH "K-flat short exact sequences, right term"]
theorem isKFlat_X₃ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

/-- Lemma 15.59.6 (2): if the right term is termwise flat and the outer terms of a short exact
sequence are K-flat, then the middle term is K-flat. -/
@[stacks 0BYH "K-flat short exact sequences, middle term"]
theorem isKFlat_X₂ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

/-- Lemma 15.59.6 (3): if the right term is termwise flat and the last two terms of a short
exact sequence are K-flat, then the left term is K-flat. -/
@[stacks 0BYH "K-flat short exact sequences, left term"]
theorem isKFlat_X₁ (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact
