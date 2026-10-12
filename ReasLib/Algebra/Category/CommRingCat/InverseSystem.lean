/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import ReasLib.CategoryTheory.InverseSystem.Cone
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

/-!
# Sequential Inverse Systems of Commutative Rings

This file supplies ring-specific predicates for a sequential inverse system of commutative
rings.  The stages and transition maps remain those of
`CategoryTheory.SequentialInverseSystem`; only properties of their underlying ring homomorphisms
are added here.
@stack 0CQF
-/

@[expose] public section

open CategoryTheory Filter

universe u

namespace CategoryTheory.SequentialInverseSystem

/-- Every successor transition in a sequential inverse system of commutative rings is
surjective. -/
@[stacks 0CQF "surjective ring inverse system"]
def Surjective (F : SequentialInverseSystem CommRingCat.{u}) : Prop :=
  ∀ n : ℕ, Function.Surjective (F.stepMap n).hom

/-- Every successor transition in a sequential inverse system of commutative rings has locally
nilpotent kernel. -/
@[stacks 0CQF "locally nilpotent kernels in a ring inverse system"]
def KernelLocallyNilpotent (F : SequentialInverseSystem CommRingCat.{u}) : Prop :=
  ∀ n : ℕ, (RingHom.ker (F.stepMap n).hom).IsLocallyNilpotent

/-- From stage `n₀` onward, every successor transition in a sequential inverse system of
commutative rings has nilpotent kernel. -/
@[stacks 0CQF "nilpotent kernels from a stage onward"]
def KernelNilpotentFrom (F : SequentialInverseSystem CommRingCat.{u}) (n₀ : ℕ) : Prop :=
  ∀ n : ℕ, n₀ ≤ n → IsNilpotent (RingHom.ker (F.stepMap n).hom)

/-- A nilpotent tail for `P` consists of a stage satisfying `P` after which all successor
transition kernels are nilpotent. -/
@[stacks 0CQF "nilpotent tail of a stagewise property"]
def NilpotentTail
    (F : SequentialInverseSystem CommRingCat.{u}) (P : ℕ → Prop) : Prop :=
  ∃ n₀ : ℕ, P n₀ ∧ F.KernelNilpotentFrom n₀

/-- A stagewise property either holds at every stage or has a nilpotent tail. -/
@[stacks 0CQF "all stages or a nilpotent tail"]
def AllOrTail
    (F : SequentialInverseSystem CommRingCat.{u}) (P : ℕ → Prop) : Prop :=
  (∀ n : ℕ, P n) ∨ F.NilpotentTail P

/-- Passing to a pointwise consequence preserves a nilpotent tail. -/
theorem NilpotentTail.mono
    {F : SequentialInverseSystem CommRingCat.{u}} {P Q : ℕ → Prop}
    (h : F.NilpotentTail P) (hPQ : ∀ n : ℕ, P n → Q n) :
    F.NilpotentTail Q := sorry

/-- Passing to a pointwise consequence preserves the all-stages-or-tail alternative. -/
theorem AllOrTail.mono
    {F : SequentialInverseSystem CommRingCat.{u}} {P Q : ℕ → Prop}
    (h : F.AllOrTail P) (hPQ : ∀ n : ℕ, P n → Q n) :
    F.AllOrTail Q := sorry

/-- A property that propagates across nilpotent successor kernels holds eventually whenever it
holds at the start of a nilpotent tail. -/
theorem NilpotentTail.eventually
    {F : SequentialInverseSystem CommRingCat.{u}} {P : ℕ → Prop}
    (h : F.NilpotentTail P)
    (hstep : ∀ n : ℕ, IsNilpotent (RingHom.ker (F.stepMap n).hom) → P n → P (n + 1)) :
    ∀ᶠ n in atTop, P n := sorry

/-- A property that propagates across nilpotent successor kernels holds eventually under the
all-stages-or-tail alternative. -/
theorem AllOrTail.eventually
    {F : SequentialInverseSystem CommRingCat.{u}} {P : ℕ → Prop}
    (h : F.AllOrTail P)
    (hstep : ∀ n : ℕ, IsNilpotent (RingHom.ker (F.stepMap n).hom) → P n → P (n + 1)) :
    ∀ᶠ n in atTop, P n := sorry

end CategoryTheory.SequentialInverseSystem

namespace CategoryTheory.Limits.Cone

/-- For a cone over a sequential inverse system of commutative rings, the ring homomorphism to
stage `n` is the composite of the map to stage `n + 1` with the successor transition. -/
theorem stageRingHom_step {F : SequentialInverseSystem CommRingCat.{u}}
    (s : Cone F) (n : ℕ) :
    (s.stageMap n).hom = (F.stepMap n).hom.comp (s.stageMap (n + 1)).hom := sorry

end CategoryTheory.Limits.Cone
