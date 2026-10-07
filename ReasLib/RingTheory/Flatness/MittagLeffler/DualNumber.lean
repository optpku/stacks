module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Presentation
public import ReasLib.RingTheory.Flatness.MittagLeffler
import ReasLib.Algebra.Category.ModuleCat.DualNumber.ResidueQuotient
import ReasLib.RingTheory.Flatness.MittagLeffler.Equiv
import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import ReasLib.RingTheory.Flatness.MittagLeffler.Quotient
import ReasLib.RingTheory.Flatness.MittagLeffler.RestrictScalars

@[expose] public section

/-!
# Mittag-Leffler modules over the dual numbers

The square-zero module attached to a presentation is free after restriction to the base ring.
It yields the standard failure of ascent of the Mittag-Leffler property to the dual numbers.
-/

universe u v w₀ w₁

open scoped DualNumber

namespace Module.MittagLeffler.DualNumber

variable {R : Type u} [CommRing R]

/-- A square-zero dual-number action preserves the Mittag-Leffler property of the underlying
module after restriction to the base ring. -/
@[stacks 05CS "square-zero module over the base"]
theorem ofSquareZero_overBase
    {X : Type v} [AddCommGroup X] [Module R X]
    (e : Module.End R X) (he : e.comp e = 0)
    (hX : Module.MittagLeffler R X) :
    Module.MittagLeffler R
      (ModuleCat.DualNumber.restrict (ModuleCat.DualNumber.ofSquareZero e he)) := sorry

/-- Reduction modulo `ε` sends a Mittag-Leffler module over the dual numbers to a
Mittag-Leffler module over the base ring. -/
@[stacks 05CS "reduction modulo epsilon"]
theorem quotient_eps_overBase
    (M : ModuleCat.{v} R[ε])
    (hM : Module.MittagLeffler R[ε] M) :
    Module.MittagLeffler R (ModuleCat.DualNumber.epsQuotient M) := sorry

/-- If a square-zero dual-number module is Mittag-Leffler, then the cokernel of its defining
endomorphism is Mittag-Leffler over the base ring. -/
@[stacks 05CS "square-zero cokernel"]
theorem quotient_range
    {X : Type v} [AddCommGroup X] [Module R X]
    (e : Module.End R X) (he : e.comp e = 0)
    (hM : Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.ofSquareZero e he)) :
    Module.MittagLeffler R (X ⧸ LinearMap.range e) := sorry

/-- The dual-number module attached to a presentation is Mittag-Leffler after restriction to the
base ring. -/
@[stacks 05CS "presentation module over the base"]
theorem ofPresentation_overBase
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M) :
    Module.MittagLeffler R (ModuleCat.DualNumber.restrict
      (ModuleCat.DualNumber.Presentation.of P)) := sorry

/-- If the dual-number module associated to `P` is Mittag-Leffler, then the module presented by
`P` is Mittag-Leffler over the base ring. -/
@[stacks 05CS "presentation quotient obstruction"]
theorem ofPresentation_quotient
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M)
    (hP : Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.Presentation.of P)) :
    Module.MittagLeffler R M := sorry

/-- If the module presented by `P` is not Mittag-Leffler, then the associated dual-number module
is not Mittag-Leffler over the dual numbers. -/
@[stacks 05CS "presentation obstruction"]
theorem not_ofPresentation
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M)
    (hM : ¬ Module.MittagLeffler R M) :
    ¬ Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.Presentation.of P) := sorry

/-- A specified non-Mittag-Leffler base module yields a dual-number module for which the property
holds after restriction to the base but fails over the dual numbers. -/
@[stacks 05CS "counterexample from a specified module"]
theorem exists_not_ascent_of
    {M₀ : ModuleCat.{v} R} (hM₀ : ¬ Module.MittagLeffler R M₀) :
    ∃ M : ModuleCat.{max u v} R[ε],
      Module.MittagLeffler R (ModuleCat.DualNumber.restrict M) ∧
        ¬ Module.MittagLeffler R[ε] M := sorry

/-- Remark 10.88.13 (05CS) (3): if some `R`-module is not Mittag-Leffler, then a module over the
dual numbers is Mittag-Leffler after restriction to `R` but is not Mittag-Leffler over the dual
numbers. -/
@[stacks 05CS "(3)"]
theorem exists_not_ascent
    (h : ∃ M₀ : ModuleCat.{v} R, ¬ Module.MittagLeffler R M₀) :
    ∃ M : ModuleCat.{max u v} R[ε],
      Module.MittagLeffler R (ModuleCat.DualNumber.restrict M) ∧
        ¬ Module.MittagLeffler R[ε] M := sorry

end Module.MittagLeffler.DualNumber
