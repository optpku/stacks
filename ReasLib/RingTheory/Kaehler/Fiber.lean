/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.Fiber.Module

/-!
# Kahler differentials over residue-field fibers

This leaf owns the canonical base-change comparison for Kahler differentials
and its residue-fiber specialization. Neither construction depends on a
smoothness or unramifiedness predicate, so those higher-level criteria can
reuse this file without owning the underlying data.

@stack 00UV
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

namespace PrimeSpectrum.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The Kahler differentials of a residue-field fiber are the base change of
the original relative Kahler module. -/
@[stacks 00UV "Kahler differentials and residue-field fibers"]
noncomputable def kaehlerBase (p : Ideal R) [p.IsPrime] :
    Ω[p.Fiber S⁄p.ResidueField] ≃ₗ[p.Fiber S]
      (p.Fiber S ⊗[S] Ω[S⁄R]) :=
  (KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField S
    (p.Fiber S)).symm

/-- Taking the residue fiber of fiber Kahler differentials at the canonical
fiber prime recovers the residue fiber of the original Kahler module. -/
@[stacks 00UV "fiber Kahler residue comparison"]
noncomputable def kaehlerResidue (q : PrimeSpectrum S) :
    (fiberPrimeAt R S q).asIdeal.Fiber
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField] ≃ₗ[S]
      q.asIdeal.Fiber Ω[S⁄R] :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ((q.asIdeal.under R).Fiber S)
        (fiberPrimeAt R S q).asIdeal.ResidueField)
      (kaehlerBase (R := R) (S := S) (q.asIdeal.under R))).restrictScalars S ≪≫ₗ
    baseChangeFiber (M := Ω[S⁄R]) q

end PrimeSpectrum.Fiber
