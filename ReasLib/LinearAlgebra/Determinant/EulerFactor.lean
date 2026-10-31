/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.LinearAlgebra.Determinant.Projective

/-!
# Euler factors of finite-projective endomorphisms

This module defines `det(1 - f T)` as the reverse characteristic polynomial of a
finite-projective endomorphism, and the local Euler factor
`det(1 - f T^d)⁻¹` as a formal power series for positive `d`.
-/

@[expose] public section

noncomputable section

universe u v

open Polynomial PowerSeries
open CategoryTheory HomologicalComplex

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The reverse characteristic polynomial `det(1 - f T)` of a finite-projective
endomorphism, computed from the matrix of the zero extension of `f` to the
chosen split free presentation. -/
def charpolyRev (f : M →ₗ[R] M) : R[X] :=
  let p := splitFreePresentation R M
  Matrix.charpolyRev (LinearMap.toMatrix' (p.iota ∘ₗ f ∘ₗ p.pi))

/-- `charpolyRev f` is the reverse characteristic polynomial of the zero
extension of `f` to the chosen split free presentation. -/
theorem charpolyRev_spec (f : M →ₗ[R] M) :
    charpolyRev f =
      let p := splitFreePresentation R M
      Matrix.charpolyRev (LinearMap.toMatrix' (p.iota ∘ₗ f ∘ₗ p.pi)) := rfl

/-- The constant term of `charpolyRev f` is `1`. -/
theorem charpolyRev_eval_zero (f : M →ₗ[R] M) : (charpolyRev f).eval 0 = 1 := by
  exact Matrix.eval_charpolyRev

/-- The reverse characteristic polynomial of the zero extension of a
finite-projective endomorphism is independent of the chosen split free
presentation. -/
theorem charpolyRev_independent (p q : SplitFreePresentation R M) (f : M →ₗ[R] M) :
    Matrix.charpolyRev (LinearMap.toMatrix' (p.iota ∘ₗ f ∘ₗ p.pi)) =
      Matrix.charpolyRev (LinearMap.toMatrix' (q.iota ∘ₗ f ∘ₗ q.pi)) := by
  let a := p.iota ∘ₗ f ∘ₗ q.pi
  let b := q.iota ∘ₗ p.pi
  have hp : ∀ x : M, p.pi (p.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) p.pi_comp_iota
  have hq : ∀ x : M, q.pi (q.iota x) = x :=
    fun x ↦ congrArg (fun h : M →ₗ[R] M ↦ h x) q.pi_comp_iota
  have hab : a ∘ₗ b = p.iota ∘ₗ f ∘ₗ p.pi := by
    ext x
    simp only [a, b, comp_apply, hq]
  have hba : b ∘ₗ a = q.iota ∘ₗ f ∘ₗ q.pi := by
    ext x
    simp only [a, b, comp_apply, hp]
  rw [← hab, ← hba, toMatrix'_comp, toMatrix'_comp,
    Matrix.charpolyRev, Matrix.charpolyRev, Matrix.map_mul, Matrix.map_mul,
    ← Matrix.smul_mul, Matrix.det_one_sub_mul_comm, Matrix.mul_smul]

/-- The local Euler factor of a finite-projective endomorphism, equal to
`det(1 - f T^d)⁻¹` for positive `d`. -/
def eulerFactor (f : M →ₗ[R] M) (d : ℕ) : PowerSeries R :=
  PowerSeries.invOfUnit (Polynomial.toPowerSeries (Polynomial.expand R d (charpolyRev f))) 1

/-- Unfolding of `eulerFactor` as `invOfUnit` of the degree-`d` expansion of
`charpolyRev`, which is its inverse for positive `d`. -/
theorem eulerFactor_def (f : M →ₗ[R] M) (d : ℕ) :
    eulerFactor f d =
      PowerSeries.invOfUnit
        (Polynomial.toPowerSeries (Polynomial.expand R d (charpolyRev f))) 1 := rfl

/-- The constant coefficient of a local Euler factor is `1`. -/
theorem constantCoeff_eulerFactor (f : M →ₗ[R] M) (d : ℕ) :
    PowerSeries.constantCoeff (eulerFactor f d) = 1 := by
  simp [eulerFactor]

/-- The Euler factor of the zero extension is independent of the chosen split
free presentation. -/
theorem eulerFactor_independent (p q : SplitFreePresentation R M)
    (f : M →ₗ[R] M) (d : ℕ) :
    PowerSeries.invOfUnit
        (Polynomial.toPowerSeries
          (Polynomial.expand R d
            (Matrix.charpolyRev (LinearMap.toMatrix' (p.iota ∘ₗ f ∘ₗ p.pi))))) 1 =
      PowerSeries.invOfUnit
        (Polynomial.toPowerSeries
          (Polynomial.expand R d
            (Matrix.charpolyRev (LinearMap.toMatrix' (q.iota ∘ₗ f ∘ₗ q.pi))))) 1 := by
  rw [charpolyRev_independent p q f]

private theorem charpolyRev_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) :
    charpolyRev f = 1 := by
  have hf : f = 0 := Subsingleton.elim _ _
  simp [charpolyRev, hf, Matrix.charpolyRev]

private theorem eulerFactor_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) (d : ℕ) :
    eulerFactor f d = 1 := by
  rw [eulerFactor, charpolyRev_of_subsingleton]
  simpa using (PowerSeries.invOfUnit_mul (1 : PowerSeries R) 1 (by simp))

end LinearMap

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [CommRing R]
variable {P : CochainComplex (ModuleCat R) ℤ} [hP : P.IsBoundedFiniteProjective]

/-- The alternating product of the termwise Euler factors of a bounded
finite-projective cochain endomorphism, equal to `det(1 - f T^d)⁻¹` for
positive `d`. -/
def eulerFactor (f : P ⟶ P) (d : ℕ) : PowerSeries R :=
  let h := hP.bounded
  let a := h.choose
  let b := h.choose_spec.choose
  ∏ i ∈ Finset.Icc a b,
    if Even i then LinearMap.eulerFactor (ModuleCat.Hom.hom (f.f i)) d
    else Polynomial.toPowerSeries
      (Polynomial.expand R d (LinearMap.charpolyRev (ModuleCat.Hom.hom (f.f i))))

/-- The cochain Euler factor is the alternating product of termwise Euler
factors over any bounding interval. -/
theorem eulerFactor_eq_prod (f : P ⟶ P) (d : ℕ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    eulerFactor f d =
      ∏ i ∈ Finset.Icc a b,
        if Even i then LinearMap.eulerFactor (ModuleCat.Hom.hom (f.f i)) d
        else Polynomial.toPowerSeries
          (Polynomial.expand R d
            (LinearMap.charpolyRev (ModuleCat.Hom.hom (f.f i)))) := by
  classical
  let term : ℤ → PowerSeries R := fun i ↦
    if Even i then LinearMap.eulerFactor (ModuleCat.Hom.hom (f.f i)) d
    else Polynomial.toPowerSeries
      (Polynomial.expand R d (LinearMap.charpolyRev (ModuleCat.Hom.hom (f.f i))))
  have outside (a b : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
      (i : ℤ) (hi : i ∉ Finset.Icc a b) : term i = 1 := by
    haveI : P.IsStrictlyGE a := ha
    haveI : P.IsStrictlyLE b := hb
    have hz : Limits.IsZero (P.X i) := by
      by_cases hia : i < a
      · exact P.isZero_of_isStrictlyGE a i hia
      · have hbi : b < i := lt_of_not_ge fun hib ↦
          hi (Finset.mem_Icc.mpr ⟨le_of_not_gt hia, hib⟩)
        exact P.isZero_of_isStrictlyLE b i hbi
    haveI : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero hz
    dsimp only [term]
    split <;> simp [LinearMap.eulerFactor_of_subsingleton,
      LinearMap.charpolyRev_of_subsingleton]
  let h := hP.bounded
  let c := h.choose
  let e := h.choose_spec.choose
  change (∏ i ∈ Finset.Icc c e, term i) = ∏ i ∈ Finset.Icc a b, term i
  calc
    _ = ∏ i ∈ Finset.Icc c e ∪ Finset.Icc a b, term i :=
      Finset.prod_subset Finset.subset_union_left fun i _ hi ↦
        outside c e h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2 i hi
    _ = _ := (Finset.prod_subset Finset.subset_union_right fun i _ hi ↦
      outside a b ha hb i hi).symm

end CochainComplex.IsBoundedFiniteProjective

namespace DerivedCategory.IsPerfect

variable {R : Type u} [CommRing R]

/-- The Euler factor of an endomorphism of a perfect object of `D(R)`,
equal to `det(1 - f T^d)⁻¹` for positive `d`. -/
def eulerFactor {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) (d : ℕ) : PowerSeries R :=
  let P := hK.choose
  let e := hK.choose_spec.choose.symm
  let instFP := hK.choose_spec.choose_spec
  let hb := instFP.bounded
  let b := hb.choose_spec.choose
  let instLE := hb.choose_spec.choose_spec.2
  -- Local instance justification (noncanonical choice): `isKProjective_of_projective` needs a chosen `IsStrictlyLE` bound, which is not unique, so it cannot be a global instance from `IsBoundedFiniteProjective`.
  haveI : P.IsStrictlyLE b := instLE
  -- Local instance justification (noncanonical choice): K-projectivity of a bounded finite-projective complex depends on that chosen `IsStrictlyLE` bound, so it is not a global instance from `IsBoundedFiniteProjective`.
  haveI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let g := e.hom ≫ f ≫ e.inv
  let iso := DerivedCategory.quotientCompQhIso (ModuleCat R)
  let g' := iso.hom.app P ≫ g ≫ iso.inv.app P
  let hmap := Function.surjInv
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient _ _).obj P)).surjective g'
  let fP := (HomotopyCategory.quotient _ _).preimage hmap
  @CochainComplex.IsBoundedFiniteProjective.eulerFactor _ _ P instFP fP d

/-- The derived Euler factor is the cochain Euler factor of a bounded
finite-projective representative. -/
theorem eulerFactor_spec {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) (d : ℕ) :
    eulerFactor hK f d =
      let P := hK.choose
      let e := hK.choose_spec.choose.symm
      let instFP := hK.choose_spec.choose_spec
      let hb := instFP.bounded
      let b := hb.choose_spec.choose
      let instLE := hb.choose_spec.choose_spec.2
      -- Local instance justification (noncanonical choice): `isKProjective_of_projective` needs a chosen `IsStrictlyLE` bound, which is not unique, so it cannot be a global instance from `IsBoundedFiniteProjective`.
      haveI : P.IsStrictlyLE b := instLE
      -- Local instance justification (noncanonical choice): K-projectivity of a bounded finite-projective complex depends on that chosen `IsStrictlyLE` bound, so it is not a global instance from `IsBoundedFiniteProjective`.
      haveI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
      let g := e.hom ≫ f ≫ e.inv
      let iso := DerivedCategory.quotientCompQhIso (ModuleCat R)
      let g' := iso.hom.app P ≫ g ≫ iso.inv.app P
      let hmap := Function.surjInv
        (CochainComplex.IsKProjective.Qh_map_bijective P
          ((HomotopyCategory.quotient _ _).obj P)).surjective g'
      let fP := (HomotopyCategory.quotient _ _).preimage hmap
      @CochainComplex.IsBoundedFiniteProjective.eulerFactor _ _ P instFP fP d :=
  rfl

/-- For positive exponent, the derived Euler factor is independent of the
bounded finite-projective representative and of any cochain lift of the
derived endomorphism. -/
theorem eulerFactor_independent {K : DerivedCategory (ModuleCat R)}
    (hK : DerivedCategory.IsPerfect K) (f : End K) (d : ℕ) (hd : 0 < d)
    {P : CochainComplex (ModuleCat R) ℤ} [P.IsBoundedFiniteProjective]
    (e : DerivedCategory.Q.obj P ≅ K) (fP : P ⟶ P)
    (hfP : DerivedCategory.Q.map fP = e.hom ≫ f ≫ e.inv) :
    eulerFactor hK f d =
      CochainComplex.IsBoundedFiniteProjective.eulerFactor fP d :=
  sorry

end DerivedCategory.IsPerfect
