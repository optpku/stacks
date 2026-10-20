/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.PowerSeries.Ideal
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import StacksCheckRecall

/-!
# Non-Mittag-Leffler modules

@stack 059U
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.MittagLeffler

/-- Example 10.91.5 (1) (Tag 059U): the `ℤ`-module `ℚ` is not Mittag-Leffler. -/
@[stacks 059U "(1)"]
theorem not_rat : ¬ Module.MittagLeffler ℤ ℚ := sorry

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Example 10.91.5 (2) (Tag 059U): a flat, countably generated, non-projective module is not
Mittag-Leffler. -/
@[stacks 059U "(2)"]
theorem not_of_flat_countablyGenerated_of_not_projective [Module.Flat R M]
    (hM : Module.CountablyGenerated R M) (hproj : ¬ Module.Projective R M) :
    ¬ Module.MittagLeffler R M := sorry

namespace PowerSeriesCounterexample

variable (k : Type u) [Field k]

/-- The quotient `k[[X]] / (X ^ n)` used in the power-series counterexamples. -/
abbrev QuotientByXPow (n : ℕ+) :=
  PowerSeries k ⧸ Ideal.span
    ({(PowerSeries.X : PowerSeries k) ^ (n : ℕ)} : Set (PowerSeries k))

/-- The product `∏ n : ℕ+, k[[X]] / (X ^ n)`. -/
abbrev Product := (n : ℕ+) → QuotientByXPow k n

/-- The sparse element whose coordinate at `2 ^ (m + 1)` is the class of `X ^ (2 ^ m)` and
whose other coordinates vanish. -/
def sparseElement : Product k := fun n =>
  @dite (QuotientByXPow k n) (∃ m : ℕ, (n : ℕ) = 2 ^ (m + 1))
    (Classical.propDecidable _)
    (fun h => Ideal.Quotient.mk _ ((PowerSeries.X : PowerSeries k) ^ (2 ^ Nat.find h)))
    (fun _ => 0)

/-- Example 10.91.5 (3) (Tag 059U): the product `∏ n : ℕ+, k[[X]] / (X ^ n)` is not
Mittag-Leffler over `k[[X]]`. -/
@[stacks 059U "(3)"]
theorem product_not_mittagLeffler :
    ¬ Module.MittagLeffler (PowerSeries k) (Product k) := sorry

/-- The principal ideal `(X)` of `k[[X]]`. -/
abbrev xIdeal : Ideal (PowerSeries k) :=
  Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))

/-- The direct sum `⨁ n : ℕ+, k[[X]] / (X ^ n)`. -/
abbrev DirectSum := Π₀ n : ℕ+, QuotientByXPow k n

/-- The canonical quotient operation for submodules of the direct sum. -/
local instance directSumHasQuotient :
    HasQuotient (DirectSum k) (Submodule (PowerSeries k) (DirectSum k)) :=
  @Submodule.hasQuotient (PowerSeries k) (DirectSum k) inferInstance inferInstance inferInstance

/-- The `(X)`-adic completion of `⨁ n : ℕ+, k[[X]] / (X ^ n)`. -/
abbrev Completion := AdicCompletion (xIdeal k) (DirectSum k)

/-- Example 10.91.5 (4) (Tag 059U): the `(X)`-adic completion of
`⨁ n : ℕ+, k[[X]] / (X ^ n)` is not Mittag-Leffler over `k[[X]]`. -/
@[stacks 059U "(4)"]
theorem completion_not_mittagLeffler :
    ¬ Module.MittagLeffler (PowerSeries k) (Completion k) := sorry

end PowerSeriesCounterexample

namespace SquareZeroPair

variable (k : Type u) [Field k]

/-- The ring `k[a, b] / (a ^ 2, a * b, b ^ 2)`. -/
abbrev Ring :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span
    ({(MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ^ 2,
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1,
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ^ 2} : Set (MvPolynomial (Fin 2) k))

/-- The class of `a` in `k[a, b] / (a ^ 2, a * b, b ^ 2)`. -/
abbrev a : Ring k := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The class of `b` in `k[a, b] / (a ^ 2, a * b, b ^ 2)`. -/
abbrev b : Ring k := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The algebra `R[T] / (a * T - b)` over `R = k[a, b] / (a ^ 2, a * b, b ^ 2)`. -/
abbrev Extension :=
  Polynomial (Ring k) ⧸ Ideal.span
    ({Polynomial.C (a k) * Polynomial.X - Polynomial.C (b k)} : Set (Polynomial (Ring k)))

/-- The quotient ring structure on `R`. -/
local instance ringCommRing : CommRing (Ring k) := Ideal.Quotient.commRing _

/-- The quotient ring structure on `R[T] / (a * T - b)`. -/
local instance extensionCommRing : CommRing (Extension k) := Ideal.Quotient.commRing _

/-- The canonical `R`-algebra structure on `R[T] / (a * T - b)`. -/
local instance extensionAlgebra : Algebra (Ring k) (Extension k) := Ideal.instAlgebraQuotient _ _

/-- The displayed single-relation algebra is finitely presented over `R`. -/
instance extensionFinitePresentation : Algebra.FinitePresentation (Ring k) (Extension k) := sorry

/-- The `R`-module `R[T] / (a * T - b)` is countably generated. -/
theorem extension_countablyGenerated : Module.CountablyGenerated (Ring k) (Extension k) := sorry

/-- The `R`-module `R[T] / (a * T - b)` is indecomposable. -/
theorem extension_indecomposable :
    CategoryTheory.Indecomposable (ModuleCat.of (Ring k) (Extension k)) := sorry

/-- Example 10.91.5 (5) (Tag 059U): the `R`-module `R[T] / (a * T - b)` is not
Mittag-Leffler for `R = k[a, b] / (a ^ 2, a * b, b ^ 2)`. -/
@[stacks 059U "(5)"]
theorem extension_not_mittagLeffler :
    ¬ Module.MittagLeffler (Ring k) (Extension k) := sorry

end SquareZeroPair

end Module.MittagLeffler

#check @Module.MittagLeffler.not_rat
#check @Module.MittagLeffler.not_of_flat_countablyGenerated_of_not_projective
#check @Module.MittagLeffler.PowerSeriesCounterexample.product_not_mittagLeffler
#check @Module.MittagLeffler.PowerSeriesCounterexample.completion_not_mittagLeffler
#check @Module.MittagLeffler.SquareZeroPair.extension_not_mittagLeffler

#print axioms Module.MittagLeffler.PowerSeriesCounterexample.sparseElement
