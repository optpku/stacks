/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Presentation
public import ReasLib.RingTheory.Flatness.MittagLeffler
import Mathlib.Algebra.Module.Presentation.Tautological
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
      (ModuleCat.DualNumber.restrict (ModuleCat.DualNumber.ofSquareZero e he)) := by
  have hmodule :
      (ModuleCat.DualNumber.restrict (ModuleCat.DualNumber.ofSquareZero e he)).isModule =
        ‹Module R X› :=
    Module.ext' _ _ (ModuleCat.DualNumber.restrictEquiv_map_smul e he)
  change @Module.MittagLeffler R X _ _
    (ModuleCat.DualNumber.restrict (ModuleCat.DualNumber.ofSquareZero e he)).isModule
  rw [hmodule]
  exact hX

/-- Reduction modulo `ε` sends a Mittag-Leffler module over the dual numbers to a
Mittag-Leffler module over the base ring. -/
@[stacks 05CS "reduction modulo epsilon"]
theorem quotient_eps_overBase
    (M : ModuleCat.{v} R[ε])
    (hM : Module.MittagLeffler R[ε] M) :
    Module.MittagLeffler R (ModuleCat.DualNumber.epsQuotient M) := by
  letI quotientModule : Module (R[ε] ⧸ _root_.DualNumber.epsIdeal R)
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M) :=
    inferInstanceAs (Module (R[ε] ⧸ _root_.DualNumber.epsIdeal R)
      (M ⧸ (_root_.DualNumber.epsIdeal R • (⊤ : Submodule R[ε] M))))
  letI quotientTower : IsScalarTower R (R[ε] ⧸ _root_.DualNumber.epsIdeal R)
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change algebraMap R (R[ε] ⧸ _root_.DualNumber.epsIdeal R) r •
          (show M ⧸ (_root_.DualNumber.epsIdeal R • ⊤) from x) =
        algebraMap R R[ε] r •
          (show M ⧸ (_root_.DualNumber.epsIdeal R • ⊤) from x)
      rw [IsScalarTower.algebraMap_apply R R[ε] (R[ε] ⧸ _root_.DualNumber.epsIdeal R)]
      exact IsScalarTower.algebraMap_smul (R[ε] ⧸ _root_.DualNumber.epsIdeal R)
        (algebraMap R R[ε] r) _
  have hQ := Module.MittagLeffler.quotient (_root_.DualNumber.epsIdeal R) hM
  have hR : Module.MittagLeffler R
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M) :=
    @Module.MittagLeffler.RestrictScalars.of_equiv R
      (R[ε] ⧸ _root_.DualNumber.epsIdeal R)
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M)
      inferInstance inferInstance inferInstance
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M).isAddCommGroup
      quotientModule
      (ModuleCat.DualNumber.EpsQuotient.restrictedIdealQuotient M).isModule quotientTower
      (_root_.DualNumber.residueAlgEquiv R) hQ
  exact (Module.MittagLeffler.equiv_iff
    (ModuleCat.DualNumber.EpsQuotient.equivIdealQuotient M)).mpr hR

/-- If a square-zero dual-number module is Mittag-Leffler, then the cokernel of its defining
endomorphism is Mittag-Leffler over the base ring. -/
@[stacks 05CS "square-zero cokernel"]
theorem quotient_range
    {X : Type v} [AddCommGroup X] [Module R X]
    (e : Module.End R X) (he : e.comp e = 0)
    (hM : Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.ofSquareZero e he)) :
    Module.MittagLeffler R (X ⧸ LinearMap.range e) := by
  exact (Module.MittagLeffler.equiv_iff
    (ModuleCat.DualNumber.OfSquareZero.epsQuotientEquiv e he)).mp
      (quotient_eps_overBase _ hM)

/-- The dual-number module attached to a presentation is Mittag-Leffler after restriction to the
base ring. -/
@[stacks 05CS "presentation module over the base"]
theorem ofPresentation_overBase
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M) :
    Module.MittagLeffler R (ModuleCat.DualNumber.restrict
      (ModuleCat.DualNumber.Presentation.of P)) := by
  exact ofSquareZero_overBase (LinearMap.TwoTerm.endomorphism P.map)
    (LinearMap.TwoTerm.endomorphism_sq P.map)
    (Module.MittagLeffler.of_projective inferInstance)

/-- If the dual-number module associated to `P` is Mittag-Leffler, then the module presented by
`P` is Mittag-Leffler over the base ring. -/
@[stacks 05CS "presentation quotient obstruction"]
theorem ofPresentation_quotient
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M)
    (hP : Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.Presentation.of P)) :
    Module.MittagLeffler R M := by
  have hQ := quotient_eps_overBase _ hP
  have hprod : Module.MittagLeffler R ((P.R →₀ R) × M) :=
    (Module.MittagLeffler.equiv_iff
      (ModuleCat.DualNumber.Presentation.quotientEquiv P)).mp hQ
  exact Module.MittagLeffler.of_retract hprod
    (LinearMap.inr R (P.R →₀ R) M) (LinearMap.snd R (P.R →₀ R) M) rfl

/-- If the module presented by `P` is not Mittag-Leffler, then the associated dual-number module
is not Mittag-Leffler over the dual numbers. -/
@[stacks 05CS "presentation obstruction"]
theorem not_ofPresentation
    {M : Type v} [AddCommGroup M] [Module R M]
    (P : Module.Presentation.{w₀, w₁} R M)
    (hM : ¬ Module.MittagLeffler R M) :
    ¬ Module.MittagLeffler R[ε]
      (ModuleCat.DualNumber.Presentation.of P) := by
  intro hP
  exact hM (ofPresentation_quotient P hP)

/-- A specified non-Mittag-Leffler base module yields a dual-number module for which the property
holds after restriction to the base but fails over the dual numbers. -/
@[stacks 05CS "counterexample from a specified module"]
theorem exists_not_ascent_of
    {M₀ : ModuleCat.{v} R} (hM₀ : ¬ Module.MittagLeffler R M₀) :
    ∃ M : ModuleCat.{max u v} R[ε],
      Module.MittagLeffler R (ModuleCat.DualNumber.restrict M) ∧
        ¬ Module.MittagLeffler R[ε] M := by
  let P := Module.Presentation.tautological R M₀
  exact ⟨ModuleCat.DualNumber.Presentation.of P,
    ofPresentation_overBase P, not_ofPresentation P hM₀⟩

/-- Remark 10.88.13 (05CS) (3): if some `R`-module is not Mittag-Leffler, then a module over the
dual numbers is Mittag-Leffler after restriction to `R` but is not Mittag-Leffler over the dual
numbers. -/
@[stacks 05CS "(3)"]
theorem exists_not_ascent
    (h : ∃ M₀ : ModuleCat.{v} R, ¬ Module.MittagLeffler R M₀) :
    ∃ M : ModuleCat.{max u v} R[ε],
      Module.MittagLeffler R (ModuleCat.DualNumber.restrict M) ∧
        ¬ Module.MittagLeffler R[ε] M := by
  obtain ⟨M₀, hM₀⟩ := h
  exact exists_not_ascent_of hM₀

end Module.MittagLeffler.DualNumber
