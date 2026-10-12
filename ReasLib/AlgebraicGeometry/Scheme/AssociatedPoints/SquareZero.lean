/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.RingTheory.MvPolynomial.SquareZero
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints

/-!
# Associated points of square-zero affine schemes

This module identifies the unique point of the spectrum of a square-zero
multivariate-polynomial quotient and computes its associated points.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open AlgebraicGeometry
open IsLocalRing
open scoped AlgebraicGeometry

namespace MvPolynomial.SquareZero

variable {σ : Type u} {k : Type v}

/-- Every point of the spectrum of a square-zero quotient over a field is its closed point. -/
theorem spec_point_eq_closedPoint [Field k]
    (x : Scheme.Spec.obj
      (Opposite.op <| CommRingCat.of (Quotient (σ := σ) (k := k)))) :
    x = closedPoint (Quotient (σ := σ) (k := k)) := by
  apply PrimeSpectrum.ext
  calc
    x.asIdeal = maximalIdeal (Quotient (σ := σ) (k := k)) := by
      apply le_antisymm
      · exact @IsLocalRing.le_maximalIdeal_of_isPrime
          (Quotient (σ := σ) (k := k)) _ _ x.asIdeal x.isPrime
      · exact @Ideal.IsLocallyNilpotent.le_prime
          (Quotient (σ := σ) (k := k)) _
          (maximalIdeal (Quotient (σ := σ) (k := k)))
          (maximalIdeal_isLocallyNilpotent (σ := σ) (k := k)) x.asIdeal x.isPrime
    _ = (closedPoint (Quotient (σ := σ) (k := k))).asIdeal := by
      simpa [closedPoint] using
        (PrimeSpectrum.asIdeal_top (Quotient (σ := σ) (k := k))).symm

/-- The spectrum of an infinite square-zero quotient over a field has no associated points. -/
theorem spec_associatedPoints_eq_empty [Field k] [Infinite σ] :
    (Scheme.Spec.obj
      (Opposite.op <| CommRingCat.of (Quotient (σ := σ) (k := k)))).associatedPoints = ∅ := by
  let R := Quotient (σ := σ) (k := k)
  let X := Scheme.Spec.obj (Opposite.op <| CommRingCat.of R)
  change X.associatedPoints = ∅
  ext x
  constructor
  · intro hx
    rw [spec_point_eq_closedPoint (σ := σ) (k := k) x] at hx ⊢
    rw [Scheme.mem_associatedPoints_iff] at hx
    rw [mem_associatedPrimesOfModule_iff] at hx
    rcases hx with ⟨_, m, hm⟩
    let x0 : X := closedPoint R
    let A := X.presheaf.stalk x0
    let M :=
      RingedSpace.stalkModuleCat
        (SheafOfModules.unit X.ringCatSheaf)
        x0
    let eR : A ≃+* R :=
      (stalkClosedPointIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let eM : M ≃ₗ[A] A :=
      RingedSpace.unitStalkLinearEquiv x0
    have hmA : Ideal.IsAssociatedToModule A A (maximalIdeal A) := by
      exact eM.isAssociatedToModule_iff.mp
        ⟨(maximalIdeal.isMaximal A).isPrime, m, hm⟩
    rcases hmA with ⟨_, a, ha⟩
    let s : R := eR a
    have hmap_maximal :
        Ideal.map eR (maximalIdeal A) = maximalIdeal R := by
      have hmax : (Ideal.map eR (maximalIdeal A)).IsMaximal := by infer_instance
      exact (IsLocalRing.isMaximal_iff R).1 hmax
    have hs_torsion :
        Ideal.torsionOf R R s = Ideal.map eR (Ideal.torsionOf A A a) := by
      have hcomap :
          Ideal.comap eR (Ideal.torsionOf R R s) = Ideal.torsionOf A A a := by
        ext y
        rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
        change eR y * eR a = 0 ↔ y * a = 0
        constructor
        · intro h
          apply eR.injective
          simpa [map_mul] using h
        · intro h
          simpa [map_mul] using congrArg eR h
      calc
        Ideal.torsionOf R R s = Ideal.map eR (Ideal.comap eR (Ideal.torsionOf R R s)) := by
          symm
          exact Ideal.map_comap_of_surjective eR.toRingHom eR.surjective _
        _ = Ideal.map eR (Ideal.torsionOf A A a) := by rw [hcomap]
    have hs : ∃ t : R, Ideal.torsionOf R R t = maximalIdeal R := by
      refine ⟨s, ?_⟩
      calc
        Ideal.torsionOf R R s = Ideal.map eR (Ideal.torsionOf A A a) := hs_torsion
        _ = Ideal.map eR (maximalIdeal A) := by rw [← ha]
        _ = maximalIdeal R := hmap_maximal
    exact (not_exists_torsionOf_eq_maximalIdeal (σ := σ) (k := k)) hs
  · intro hx
    exact hx.elim

end MvPolynomial.SquareZero
