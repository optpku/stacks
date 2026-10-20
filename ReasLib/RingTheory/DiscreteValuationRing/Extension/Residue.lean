/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification

@[expose] public section

/-!
# Residue Degrees of Discrete Valuation Ring Extensions

This module gives the extension-level residue degree and bridges it to the
canonical inertia degree of maximal ideals.

@stack 09E4
@stack 0BJ6
-/

universe u v

open Ideal IsLocalRing

namespace IsExtensionOfDiscreteValuationRings

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]

/-- Definition 15.112.1 (4): the residue degree of a finite extension of discrete valuation
rings. -/
@[stacks 09E4 "residue degree"]
noncomputable def residueDegree [IsExtensionOfDiscreteValuationRings A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)] : ℕ :=
  Module.finrank (ResidueField A) (ResidueField B)

/-- The residue degree agrees with the canonical inertia degree of the maximal ideals. -/
theorem residueDegree_eq_inertiaDeg [IsExtensionOfDiscreteValuationRings A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)] :
    residueDegree A B = (maximalIdeal A).inertiaDeg' (maximalIdeal B) := sorry
-- Proof strategy: unfold `residueDegree`, use that the two maximal ideals form the canonical
-- lying-over pair of the local algebra map, and apply `Ideal.inertiaDeg'_eq_inertiaDeg` together
-- with the residue-field/fraction-field identification for maximal-ideal quotients.

/-- The residue degree computes as the finite dimension of the induced residue-field extension. -/
theorem residueDegree_eq_finrank [IsExtensionOfDiscreteValuationRings A B]
    [FiniteDimensional (ResidueField A) (ResidueField B)] :
    residueDegree A B = Module.finrank (ResidueField A) (ResidueField B) := sorry
-- Proof strategy: unfold `residueDegree`; the right-hand side is its defining expression.

/-- The parameter ideal of a DVR maps into the corresponding parameter ideal in
an extension. This is the canonical quotient-algebra compatibility used by the
special-fiber API below. -/
theorem specialFiber_ideal_le_comap
    (π : A) :
    Ideal.span ({π} : Set A) ≤
      Ideal.comap (algebraMap A B)
        (Ideal.span ({algebraMap A B π} : Set B)) := sorry
-- Proof strategy: apply `Ideal.span_le`; the image of the sole generator belongs to the target
-- principal ideal by `Ideal.subset_span`, and `Ideal.mem_comap` translates this membership back.

/-- The target special fiber is canonically an algebra over the source special
fiber. -/
@[stacks 0BJ6 "algebra structure on the special fiber of a DVR extension"]
instance specialFiberAlgebra (π : A) :
    Algebra (A ⧸ Ideal.span ({π} : Set A))
      (B ⧸ Ideal.span ({algebraMap A B π} : Set B)) :=
  Ideal.Quotient.algebraQuotientOfLEComap (specialFiber_ideal_le_comap (A := A) (B := B) π)

/-- For a weakly unramified DVR extension, quotienting by an irreducible parameter gives the
canonical residue-field extension; hence residue-field separability implies separability of the
corresponding special fibers. -/
@[stacks 0BJ6]
theorem specialFiber_isSeparable_of_irreducible
    [IsExtensionOfDiscreteValuationRings A B] [WeaklyUnramified A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {π : A} (hπ : Irreducible π) :
    Algebra.IsSeparable
      (A ⧸ Ideal.span ({π} : Set A))
      (B ⧸ Ideal.span ({algebraMap A B π} : Set B)) := sorry
-- Proof strategy: rewrite the source ideal with `hπ.maximalIdeal_eq`; weak unramifiedness and
-- `WeaklyUnramified.map_maximalIdeal_eq` identify the target principal ideal with
-- `maximalIdeal B`. Transport the assumed residue-field separability across the canonical
-- quotient-to-residue-field algebra equivalences.

end

end IsExtensionOfDiscreteValuationRings
