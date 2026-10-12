/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion
public import ReasLib.CategoryTheory.Linear.PrincipalPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Power presentations of principal torsion systems

A power presentation records the short exact rows
`F 1 ⟶ F (n + 1) ⟶ F n` and identifies the return endomorphism of `F (n + 1)` with the
`n`th power of a scalar.  This is the representation-independent form of the second condition
in the standard characterization of principal torsion systems.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- A chosen presentation by the short exact power rows
`F 1 ⟶ F (n + 1) ⟶ F n`. -/
@[stacks 0H39 "power presentation of a principal torsion system"]
structure PowerPresentation (r : R) (F : SequentialInverseSystem C) where
  /-- The inclusion of the first positive stage into stage `n + 1`. -/
  inclusion : ∀ n : ℕ+, F.obj (op 1) ⟶ F.obj (op ((n : ℕ) + 1))
  /-- The inclusion is killed by the successor transition. -/
  inclusion_comp_stepMap : ∀ n : ℕ+,
    inclusion n ≫ F.stepMap (n : ℕ) = 0
  /-- Each power row is short exact. -/
  shortExact : ∀ n : ℕ+,
    (ShortComplex.mk (inclusion n) (F.stepMap (n : ℕ))
      (inclusion_comp_stepMap n)).ShortExact
  /-- Projection to the first stage followed by inclusion is the corresponding scalar power. -/
  toFirst_comp_inclusion : ∀ n : ℕ+,
    toFirst F n ≫ inclusion n =
      CategoryTheory.Linear.PrincipalPower.smulPow r
        (F.obj (op ((n : ℕ) + 1))) (n : ℕ)

/-- Inclusion maps with short exact power rows and scalar-power return maps determine a
power presentation. -/
def PowerPresentation.ofInclusions {r : R} {F : SequentialInverseSystem C}
    (inclusions : ∀ index : ℕ+, F.obj (op 1) ⟶ F.obj (op ((index : ℕ) + 1)))
    (h_zero : ∀ index : ℕ+, inclusions index ≫ F.stepMap (index : ℕ) = 0)
    (h_shortExact : ∀ index : ℕ+,
      (ShortComplex.mk (inclusions index) (F.stepMap (index : ℕ))
        (h_zero index)).ShortExact)
    (h_scalar : ∀ index : ℕ+, toFirst F index ≫ inclusions index =
      CategoryTheory.Linear.PrincipalPower.smulPow r
        (F.obj (op ((index : ℕ) + 1))) (index : ℕ)) : PowerPresentation r F :=
  { inclusion := inclusions
    inclusion_comp_stepMap := h_zero
    shortExact := h_shortExact
    toFirst_comp_inclusion := h_scalar }

/-- The short exact row selected by a power presentation. -/
abbrev PowerPresentation.row {r : R} {F : SequentialInverseSystem C}
    (P : PowerPresentation r F) (n : ℕ+) : ShortComplex C :=
  ShortComplex.mk (P.inclusion n) (F.stepMap (n : ℕ))
    (P.inclusion_comp_stepMap n)

/-- A row selected by a power presentation is short exact. -/
theorem PowerPresentation.row_shortExact
    {r : R} {F : SequentialInverseSystem C}
    (P : PowerPresentation r F) (n : ℕ+) :
    (P.row n).ShortExact := sorry

/-- A sequential inverse system admits a presentation by principal-power rows.  The presentation
is explicit data, while this predicate records only its existence. -/
@[stacks 0H39 "existence of a principal-power presentation"]
def IsPowerPresented (r : R) (F : SequentialInverseSystem C) : Prop :=
  Nonempty (PowerPresentation r F)

/-- Existence of a power presentation in terms of its stagewise short exact rows. -/
theorem isPowerPresented_iff (r : R) (F : SequentialInverseSystem C) :
    IsPowerPresented r F ↔
      ∀ n : ℕ+, ∃ (ι : F.obj (op 1) ⟶ F.obj (op ((n : ℕ) + 1)))
        (hι : ι ≫ F.stepMap (n : ℕ) = 0),
        (ShortComplex.mk ι (F.stepMap (n : ℕ)) hι).ShortExact ∧
          toFirst F n ≫ ι =
            CategoryTheory.Linear.PrincipalPower.smulPow r
              (F.obj (op ((n : ℕ) + 1))) (n : ℕ) := sorry

/-- A power presentation exists exactly when every stage `n ≥ 1` admits a short exact power
row with the required scalar-power return endomorphism. -/
@[stacks 0H39 "one-based principal-power presentation"]
theorem isPowerPresented_iff_one_le (r : R) (F : SequentialInverseSystem C) :
    IsPowerPresented r F ↔
      ∀ n : ℕ, 1 ≤ n →
        ∃ (ι : F.obj (op 1) ⟶ F.obj (op (n + 1)))
          (hι : ι ≫ F.stepMap n = 0),
          (ShortComplex.mk ι (F.stepMap n) hι).ShortExact ∧
            F.transitionMap (Nat.succ_le_succ (Nat.zero_le n)) ≫ ι =
              CategoryTheory.Linear.PrincipalPower.smulPow r
                (F.obj (op (n + 1))) n := sorry

section Abelian

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- A principal torsion presentation exists exactly when a principal-power presentation exists. -/
@[stacks 0H39 "step and power presentations are equivalent"]
theorem isPowerPresented_iff_isPresented
    (r : R) (F : SequentialInverseSystem C) :
    IsPowerPresented r F ↔ IsPresented r F := sorry

end Abelian

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion
