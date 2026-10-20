/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Splitting
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Monic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Truncating chosen splittings of simplicial objects

This module restricts a chosen splitting of a simplicial object to a finite truncation and
records the induced splitness and monicity API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {X : SimplicialObject C}

namespace Splitting

namespace truncation

/-- The restricted splitting cofan is colimiting at every truncated simplex. -/
@[stacks 017P "colimit decomposition after truncating a splitting"]
def isColimit (s : Splitting X) {n : ℕ}
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    IsColimit (Truncated.Splitting.cofan'
      (fun m : Fin (n + 1) ↦ s.N m.1) ((SimplicialObject.truncation n).obj X)
      (fun m : Fin (n + 1) ↦ s.ι m.1) Δ) :=
  s.isColimit (op Δ.unop.obj)

end truncation

/-- Restrict a chosen splitting of a simplicial object to its degree-`n` truncation. -/
@[stacks 017P "truncation of a chosen splitting"]
def truncation (s : Splitting X) (n : ℕ) :
    Truncated.Splitting ((SimplicialObject.truncation n).obj X) where
  N m := s.N m.1
  ι m := s.ι m.1
  isColimit' := truncation.isColimit s

/-- The degree-`m` summand of a truncated splitting is the original degree-`m` summand. -/
@[simp, stacks 017P "summands after truncating a splitting"]
theorem truncation_N (s : Splitting X) {n : ℕ} (m : Fin (n + 1)) :
    (s.truncation n).N m = s.N m.1 := sorry

/-- The distinguished map of a truncated splitting is the original distinguished map in the
same degree. -/
@[simp, stacks 017P "summand maps after truncating a splitting"]
theorem truncation_ι (s : Splitting X) {n : ℕ} (m : Fin (n + 1)) :
    (s.truncation n).ι m = s.ι m.1 := sorry

namespace IsMonic

/-- Truncation preserves an explicit proof that a chosen splitting is monic. -/
@[stacks 017P "monicity after truncating a splitting"]
theorem truncation {s : Splitting X} (hs : s.IsMonic) (n : ℕ) :
    (s.truncation n).IsMonic := sorry

end IsMonic

namespace truncation

/-- Typeclass transport of monicity from a chosen splitting to its finite truncation. -/
@[stacks 017P "monicity instance after truncating a splitting"]
instance isMonic (s : Splitting X) [s.IsMonic] (n : ℕ) :
    (s.truncation n).IsMonic := sorry

end truncation

end Splitting

namespace IsSplit

/-- Every truncation of a split simplicial object is split. -/
@[stacks 017P "splitness after truncation"]
theorem truncation (hX : IsSplit X) (n : ℕ) :
    Truncated.IsSplit ((SimplicialObject.truncation n).obj X) := sorry

end IsSplit

end CategoryTheory.SimplicialObject
