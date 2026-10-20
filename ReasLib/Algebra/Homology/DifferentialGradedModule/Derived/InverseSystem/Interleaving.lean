/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.HomOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Interleavings of global left derived module systems

An interleaving uses a common strictly increasing reindexing and alternating cross-index
morphisms between two objects of the global left derived category.  Consecutive alternating
morphisms recover the canonical transition of the corresponding object.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.Derived.Left

variable {R : Type u} [CommRing R]

/-- The index of an even stage is at most the following odd stage after an order-preserving
reindexing. -/
theorem evenOddLE (r : ℕ →o ℕ) (i : ℕ) :
    r (2 * i) ≤ r (2 * i + 1) := sorry

/-- The index of an odd stage is at most the following even stage after an order-preserving
reindexing. -/
theorem oddEvenLE (r : ℕ →o ℕ) (i : ℕ) :
    r (2 * i + 1) ≤ r (2 * (i + 1)) := sorry

/-- Consecutive even indices remain ordered after an order-preserving reindexing. -/
theorem evenSpanLE (r : ℕ →o ℕ) (i : ℕ) :
    r (2 * i) ≤ r (2 * (i + 1)) := sorry

/-- Consecutive odd indices remain ordered after an order-preserving reindexing. -/
theorem oddSpanLE (r : ℕ →o ℕ) (i : ℕ) :
    r (2 * i + 1) ≤ r (2 * (i + 1) + 1) := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): alternating cross-index morphisms between two objects of the
global left derived category along a common strictly increasing reindexing. -/
@[stacks 0GZI "interleavings of global left derived module systems"]
structure Interleaving
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N N' : Category.{u, x, v} A) where
  /-- The common reindexing of the two global derived systems. -/
  reindex : ℕ →o ℕ
  /-- The common reindexing is strictly increasing. -/
  strictMono : StrictMono reindex
  /-- The cross-index morphism from the next even stage of `N` to the intervening odd stage of
  `N'`. -/
  evenToOdd (i : ℕ) :
    HomOver A N N' (oddEvenLE reindex i)
  /-- The cross-index morphism from an odd stage of `N'` to the preceding even stage of `N`. -/
  oddToEven (i : ℕ) :
    HomOver A N' N (evenOddLE reindex i)
  /-- Two consecutive alternating cross-index morphisms recover the corresponding transition
  of `N`. -/
  evenComp (i : ℕ) :
    HomOver.comp (evenToOdd i) (oddToEven i) =
      HomOver.transition A N (evenSpanLE reindex i)
  /-- Two consecutive alternating cross-index morphisms recover the corresponding transition
  of `N'`. -/
  oddComp (i : ℕ) :
    HomOver.comp (oddToEven (i + 1)) (evenToOdd i) =
      HomOver.transition A N' (oddSpanLE reindex i)

end DifferentialGradedModule.InverseSystem.Derived.Left
