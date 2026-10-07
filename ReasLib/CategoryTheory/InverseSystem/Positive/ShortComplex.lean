module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.InverseSystem.Positive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Step rows in positive inverse systems

This file packages a compatible family `K n ⟶ F (n + 1)` with the successor maps of a positive
inverse system.  It is independent of sheaves, modules, ideal powers, and cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.PNatInverseSystem

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The short-complex row `K n ⟶ F (n + 1) ⟶ F n` at a positive stage of an inverse system. -/
@[stacks 0GYM "step row in a positive inverse system"]
abbrev stepRow
    (F : PNatInverseSystem C) (K : ℕ+ → C)
    (ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1))
    (hι : ∀ n : ℕ+, ι n ≫ F.stepMap n = 0) (n : ℕ+) :
    ShortComplex C :=
  ShortComplex.mk (ι n) (F.stepMap n) (hι n)

/-- Every successor row of a compatible family over a positive inverse system is short exact. -/
@[stacks 0GYM "short exact step rows in a positive inverse system"]
def IsStepShortExact
    (F : PNatInverseSystem C) (K : ℕ+ → C)
    (ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1))
    (hι : ∀ n : ℕ+, ι n ≫ F.stepMap n = 0) : Prop :=
  ∀ n : ℕ+, (F.stepRow K ι hι n).ShortExact

/-- Extract short exactness of one successor row. -/
theorem IsStepShortExact.shortExact
    {F : PNatInverseSystem C} {K : ℕ+ → C}
    {ι : ∀ n : ℕ+, K n ⟶ F.stage (n + 1)}
    {hι : ∀ n : ℕ+, ι n ≫ F.stepMap n = 0}
    (h : F.IsStepShortExact K ι hι) (n : ℕ+) :
    (F.stepRow K ι hι n).ShortExact := sorry

end CategoryTheory.PNatInverseSystem
