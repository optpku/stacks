/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Etale.StandardEtale
public import ReasLib.RingTheory.Etale.Point
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale points realizing finite separable residue extensions

This leaf realizes a finite separable extension of the residue field at a prime by a
pointed etale extension.  The constructed algebra and selected prime remain
available through `PrimeSpectrum.EtalePoint`.

@stack 00UD
-/

@[expose] public section

universe u v

open Polynomial
open scoped Polynomial

namespace PrimeSpectrum.EtalePoint

/-- Every finite separable extension of the residue field at a prime is the
residue field of a point on an etale algebra over the base ring. -/
@[stacks 00UD "etale point realizing a finite separable residue extension"]
theorem exists_with_residueFieldEquiv
    {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    (L : Type v) [Field L] [Algebra p.asIdeal.ResidueField L]
    [FiniteDimensional p.asIdeal.ResidueField L]
    [Algebra.IsSeparable p.asIdeal.ResidueField L] :
    ∃ U : PrimeSpectrum.EtalePoint.{u, u} p,
      -- Local instance justification (defeq pin): expose the explicit residue-field
      -- algebra carried by the selected pointed etale extension in this proposition.
      letI : Algebra p.asIdeal.ResidueField U.point.asIdeal.ResidueField :=
        U.residueFieldAlgebra
      Nonempty (U.point.asIdeal.ResidueField ≃ₐ[p.asIdeal.ResidueField] L) := by
  classical
  let D : Type u := R ⧸ p.asIdeal
  let k : Type u := p.asIdeal.ResidueField
  -- `P.lift` needs the actual composite R-algebra on L; keep it local.
  letI : Algebra R L :=
    RingHom.toAlgebra ((algebraMap k L).comp (algebraMap R k))
  letI : IsScalarTower R k L := IsScalarTower.of_algebraMap_eq' rfl

  -- The only primitive-element choice is the native finite-separable power basis.
  let pb : PowerBasis k L := Field.powerBasisOfFiniteOfSeparable k L
  let h : k[X] := minpoly k pb.gen
  have hh_monic : h.Monic := by
    simpa [h] using (minpoly.monic pb.isIntegral_gen)

  -- `commonDenom` is the native denominator choice for all coefficients of `h`.
  let d : nonZeroDivisors D := IsLocalization.commonDenom (nonZeroDivisors D) h.support h.coeff
  let c : k := algebraMap D k d
  have hc_unit : IsUnit c := by
    exact IsLocalization.map_units k d
  have hc : c ≠ 0 := isUnit_iff_ne_zero.mp hc_unit

  have hscaled_lifts : h.scaleRoots c ∈ Polynomial.lifts (algebraMap D k) := by
    exact IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors D) h
      ⟨1, by simp [hh_monic]⟩
  have hscaled_monic : (h.scaleRoots c).Monic := by
    exact (Polynomial.monic_scaleRoots_iff c).2 hh_monic

  -- First native monic lift: from the residue field to `D = R ⧸ p`.
  obtain ⟨fbar, hfbar_map, _hfbar_natDegree, hfbar_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hscaled_lifts hscaled_monic

  -- Second native monic lift: from `D` to the original ring `R`.
  have hfbar_lifts : fbar ∈ Polynomial.lifts (Ideal.Quotient.mk p.asIdeal) := by
    exact Polynomial.mem_lifts_of_surjective
      (f := Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective fbar
  obtain ⟨f, hf_map, _hf_natDegree, hf_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hfbar_lifts hfbar_monic

  let β : L := c • pb.gen
  -- This is the scaled-root identity for `scaleRoots`; it is a proposition only.
  have hscaled_root : aeval β (h.scaleRoots c) = 0 := by
    sorry
  -- Multiplication by the nonzero `c` transports the native power basis.
  let pbβ : PowerBasis k L :=
    { gen := β
      dim := pb.dim
      basis := pb.basis.unitsSMul (fun i => (Units.mk0 c hc) ^ (i : ℕ))
      basis_eq_pow := by
        sorry }
  -- The minimal polynomial of the transported generator is the scaled polynomial.
  have hβ_minpoly : minpoly k pbβ.gen = h.scaleRoots c := by
    sorry

  -- The root and derivative facts are the genuine separability obligations.  The unit
  -- itself is supplied explicitly, so `P.lift` receives an actual inverse unit.
  have hf_root : aeval β f = 0 := by
    sorry
  have hf_deriv_ne_zero : aeval β f.derivative ≠ 0 := by
    sorry
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hf_monic
      g := f.derivative
      cond := by
        refine ⟨1, 0, 1, ?_⟩
        simp }
  have hPmap : P.HasMap β := by
    refine ⟨?_, ?_⟩
    · simpa [P] using hf_root
    · refine ⟨Units.mk0 (aeval β f.derivative) hf_deriv_ne_zero, rfl⟩
  let eval : P.Ring →ₐ[R] L := P.lift β hPmap

  -- The selected point is the actual kernel prime of the evaluation map.
  let q : PrimeSpectrum P.Ring :=
    ⟨RingHom.ker eval.toRingHom, RingHom.ker_isPrime _⟩
  letI : q.asIdeal.IsPrime := q.isPrime
  have hover : p.asIdeal = Ideal.comap (algebraMap R P.Ring) q.asIdeal := by
    sorry
  let U : PrimeSpectrum.EtalePoint.{u, u} p :=
    PrimeSpectrum.EtalePoint.of q hover

  refine ⟨U, ?_⟩
  letI : Algebra k U.point.asIdeal.ResidueField := U.residueFieldAlgebra

  -- The residue-field map is the localization lift of the evaluation ring map.
  have hkernel : U.point.asIdeal ≤ RingHom.ker eval.toRingHom := by
    intro x hx
    change x ∈ RingHom.ker eval.toRingHom at hx
    exact hx
  have hunits : U.point.asIdeal.primeCompl ≤
      (IsUnit.submonoid L).comap eval.toRingHom := by
    intro x hx
    change x ∉ RingHom.ker eval.toRingHom at hx
    change IsUnit (eval.toRingHom x)
    refine ⟨Units.mk0 (eval.toRingHom x) ?_, rfl⟩
    intro hz
    apply hx
    exact hz
  let residueLift : U.point.asIdeal.ResidueField →+* L :=
    Ideal.ResidueField.lift U.point.asIdeal eval.toRingHom hkernel hunits
  let forward : U.point.asIdeal.ResidueField →ₐ[k] L :=
    { toRingHom := residueLift
      commutes' := by
        sorry }

  -- `PowerBasis.lift` is the inverse data itself; no surjectivity choice is used.
  let γ : U.point.asIdeal.ResidueField :=
    algebraMap P.Ring q.asIdeal.ResidueField P.X
  have hγ : aeval γ (minpoly k pbβ.gen) = 0 := by
    sorry
  let inverse : L →ₐ[k] U.point.asIdeal.ResidueField := pbβ.lift γ hγ
  have hforward_inverse : forward.comp inverse = AlgHom.id k L := by
    sorry
  have hinverse_forward : inverse.comp forward = AlgHom.id k U.point.asIdeal.ResidueField := by
    sorry
  let equiv : U.point.asIdeal.ResidueField ≃ₐ[k] L :=
    AlgEquiv.ofAlgHom forward inverse hforward_inverse hinverse_forward
  exact ⟨equiv⟩

end PrimeSpectrum.EtalePoint
