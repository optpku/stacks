/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

/-!
# Sequential Lower Truncations for a T-Structure

An antitone sequence of integer cutoffs determines a sequential inverse
system of lower truncations for any `t`-structure. This file owns the core
construction independently of derived categories, canonical `t`-structures,
and the particular sequence `n ↦ -n`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.TStructure.TruncGE.Sequence

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

/-- The object at position `n` in the lower-truncation sequence selected by
the cutoff function `p`. -/
abbrev stage (t : TStructure C) (X : C) (p : ℕ → ℤ) (n : ℕ) : C :=
  (t.truncGE (p n)).obj X

/-- The successor transition in the lower-truncation sequence selected by an
antitone cutoff function. -/
abbrev step (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    stage t X p (n + 1) ⟶ stage t X p n :=
  (t.natTransTruncGEOfLE (p (n + 1)) (p n)
    (hp (Nat.le_succ n))).app X

/-- The sequential inverse system of lower truncations selected by an
antitone sequence of integer cutoffs. -/
@[stacks 0H72]
def ofAntitone (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) : SequentialInverseSystem C :=
  Functor.ofOpSequence (step t X p hp)

/-- The object at `n` in an antitone lower-truncation sequence is the lower
truncation at `p n`. -/
@[simp]
theorem ofAntitone_obj (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (ofAntitone t X p hp).obj (op n) = stage t X p n := sorry

/-- The successor map of an antitone lower-truncation sequence is its
declared truncation comparison. -/
@[simp]
theorem ofAntitone_stepMap (t : TStructure C) (X : C) (p : ℕ → ℤ)
    (hp : Antitone p) (n : ℕ) :
    (ofAntitone t X p hp).stepMap n = step t X p hp n := sorry

/-- Every transition of an antitone lower-truncation sequence is the direct
canonical comparison between the corresponding truncation functors. -/
theorem ofAntitone_transitionMap (t : TStructure C) (X : C)
    (p : ℕ → ℤ) (hp : Antitone p) {m n : ℕ} (h : m ≤ n) :
    (ofAntitone t X p hp).transitionMap h =
      (t.natTransTruncGEOfLE (p n) (p m) (hp h)).app X := sorry

end

end CategoryTheory.Triangulated.TStructure.TruncGE.Sequence
