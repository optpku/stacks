/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Data.PNat.Order
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal torsion inverse systems

A principal torsion presentation of a sequential inverse system records the short exact rows
`F n ⟶ F (n + 1) ⟶ F 1` together with the requirement that the successor transition followed
by the first map is scalar multiplication by a fixed element.  The definition is independent of
sheaves and cohomology.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.SequentialInverseSystem

variable {R : Type w} [Semiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

namespace PrincipalTorsion

/-- The projection from stage `n + 1` to the first positive stage of a sequential inverse
system. -/
abbrev toFirst (F : SequentialInverseSystem C) (n : ℕ+) :
    F.obj (op ((n : ℕ) + 1)) ⟶ F.obj (op 1) :=
  F.transitionMap (Nat.succ_le_succ (Nat.zero_le (n : ℕ)))

/-- A chosen presentation of a sequential inverse system by principal torsion extensions. -/
@[stacks 0H39 "principal torsion presentation of a sequential inverse system"]
structure Presentation (r : R) (F : SequentialInverseSystem C) where
  /-- The inclusion from one positive stage into its successor. -/
  inclusion : ∀ n : ℕ+, F.obj (op (n : ℕ)) ⟶ F.obj (op ((n : ℕ) + 1))
  /-- The inclusion is killed by projection to the first positive stage. -/
  inclusion_comp_toFirst : ∀ n : ℕ+, inclusion n ≫ toFirst F n = 0
  /-- Each principal extension row is short exact. -/
  shortExact : ∀ n : ℕ+,
    (ShortComplex.mk (inclusion n) (toFirst F n) (inclusion_comp_toFirst n)).ShortExact
  /-- Returning one step and then including is multiplication by the chosen scalar. -/
  stepMap_comp_inclusion : ∀ n : ℕ+,
    F.stepMap (n : ℕ) ≫ inclusion n = r • 𝟙 (F.obj (op ((n : ℕ) + 1)))

/-- Inclusion maps with short exact extension rows and scalar return maps determine a
principal torsion presentation. -/
def Presentation.ofInclusions {r : R} {F : SequentialInverseSystem C}
    (inclusions : ∀ index : ℕ+,
      F.obj (op (index : ℕ)) ⟶ F.obj (op ((index : ℕ) + 1)))
    (h_zero : ∀ index : ℕ+, inclusions index ≫ toFirst F index = 0)
    (h_shortExact : ∀ index : ℕ+,
      (ShortComplex.mk (inclusions index) (toFirst F index) (h_zero index)).ShortExact)
    (h_scalar : ∀ index : ℕ+,
      F.stepMap (index : ℕ) ≫ inclusions index =
        r • 𝟙 (F.obj (op ((index : ℕ) + 1)))) : Presentation r F :=
  { inclusion := inclusions
    inclusion_comp_toFirst := h_zero
    shortExact := h_shortExact
    stepMap_comp_inclusion := h_scalar }

/-- The short exact row at a positive stage of a principal torsion presentation. -/
abbrev row {r : R} {F : SequentialInverseSystem C}
    (P : Presentation r F) (n : ℕ+) : ShortComplex C :=
  ShortComplex.mk (P.inclusion n) (toFirst F n) (P.inclusion_comp_toFirst n)

/-- The row exposed by a principal torsion presentation is short exact. -/
theorem Presentation.row_shortExact
    {r : R} {F : SequentialInverseSystem C}
    (P : Presentation r F) (n : ℕ+) :
    (row P n).ShortExact := sorry

/-- A sequential inverse system is a principal `r`-torsion tower when it admits a principal
torsion presentation. -/
@[stacks 0H39 "principal torsion sequential inverse system"]
def IsPresented (r : R) (F : SequentialInverseSystem C) : Prop :=
  Nonempty (Presentation r F)

/-- A principal torsion tower is equivalently a family of short exact extension
rows whose return maps are multiplication by the chosen scalar. -/
theorem isPresented_iff
    (r : R) (F : SequentialInverseSystem C) :
    IsPresented r F ↔
      ∀ n : ℕ+, ∃ (ι : F.obj (op (n : ℕ)) ⟶ F.obj (op ((n : ℕ) + 1)))
        (hι : ι ≫ toFirst F n = 0),
        (ShortComplex.mk ι (toFirst F n) hι).ShortExact ∧
          F.stepMap (n : ℕ) ≫ ι = r • 𝟙 (F.obj (op ((n : ℕ) + 1))) := sorry

/-- A principal torsion presentation exists exactly when every stage `n ≥ 1` admits a short
exact extension row whose return endomorphism is scalar multiplication. -/
@[stacks 0H39 "one-based principal torsion presentation"]
theorem isPresented_iff_one_le
    (r : R) (F : SequentialInverseSystem C) :
    IsPresented r F ↔
      ∀ n : ℕ, 1 ≤ n →
        ∃ (ι : F.obj (op n) ⟶ F.obj (op (n + 1)))
          (hι : ι ≫ F.transitionMap (Nat.succ_le_succ (Nat.zero_le n)) = 0),
          (ShortComplex.mk ι
            (F.transitionMap (Nat.succ_le_succ (Nat.zero_le n))) hι).ShortExact ∧
            F.stepMap n ≫ ι = r • 𝟙 (F.obj (op (n + 1))) := sorry

end PrincipalTorsion

end CategoryTheory.SequentialInverseSystem
