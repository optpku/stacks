/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
import Mathlib.Data.Int.Interval

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace DivisorComplexChart

/-- The finite product of the degreewise determinantal ideals attached to an affine
divisor-complex chart. -/
noncomputable def productIdeal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    Ideal Γ(X, C.U) :=
  ∏ᶠ i : ℤ,
    @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal
      _ _ C.generator C.model i
        (@HomologicalComplex.IsTermwiseFiniteFree.out _ _ _ _ C.model C.finiteFree i).2
        (@HomologicalComplex.IsTermwiseFiniteFree.out
          _ _ _ _ C.model C.finiteFree (i + 1)).1
        (@HomologicalComplex.IsTermwiseFiniteFree.out
          _ _ _ _ C.model C.finiteFree (i + 1)).2

private theorem fittingIdeal_eq_top_of_subsingleton (R N : Type u) [CommRing R]
    [AddCommGroup N] [Module R N] [Subsingleton N] (k : ℕ) :
    fittingIdeal R N k = ⊤ := by
  classical
  by_cases hR : Subsingleton R
  · letI := hR
    exact Subsingleton.elim _ _
  · letI : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    apply top_unique
    refine le_sInf ?_
    rintro J ⟨⟨n, π, hπ⟩, rfl⟩
    apply ((Ideal.eq_top_iff_one _).mpr ?_).ge
    change 1 ∈ Matrix.minorIdeal (n - k)
      (fun a b ↦ b.1 a : Matrix (Fin n) (LinearMap.ker π) R)
    let e : Fin (n - k) ↪ Fin n := Fin.castLEEmb (Nat.sub_le n k)
    let v : Fin (n - k) ↪ LinearMap.ker π :=
      { toFun := fun j ↦ ⟨Pi.single (e j) 1, by exact Subsingleton.elim _ _⟩
        inj' := by
          intro a b hab
          by_contra hne
          have h := congrArg (fun x : LinearMap.ker π ↦ x.1 (e a)) hab
          simp [e.injective.eq_iff, hne] at h }
    have hv : (fun a b : Fin (n - k) ↦ (v b).1 (e a)) =
        (1 : Matrix (Fin (n - k)) (Fin (n - k)) R) := by
      ext a b
      simp [v, Pi.single_apply, e.injective.eq_iff, Matrix.one_apply]
    have hm :
        Matrix.det (Matrix.submatrix
          (fun a b ↦ b.1 a : Matrix (Fin n) (LinearMap.ker π) R) e v) ∈
          Matrix.minorIdeal (n - k) (fun a b ↦ b.1 a : Matrix (Fin n) (LinearMap.ker π) R) :=
      Ideal.subset_span ⟨(e, v), rfl⟩
    change Matrix.det (fun a b : Fin (n - k) ↦ (v b).1 (e a)) ∈ _ at hm
    simpa only [hv, Matrix.det_one] using hm

/-- Only finitely many degreewise determinantal ideals of an affine divisor-complex chart
differ from the unit ideal. -/
theorem ideal_hasFiniteMulSupport {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    Function.HasFiniteMulSupport fun i : ℤ ↦ C.ideal i := by
  obtain ⟨a, ha⟩ := C.bounded.1
  obtain ⟨b, hb⟩ := C.bounded.2
  letI := ha
  letI := hb
  apply (Set.finite_Icc (a - 1) b).subset
  intro i hi
  by_contra hmem
  have hzero : CategoryTheory.Limits.IsZero (C.model.X i) ∧
      CategoryTheory.Limits.IsZero (C.model.X (i + 1)) := by
    by_cases hia : i < a - 1
    · exact ⟨C.model.isZero_of_isStrictlyGE a i (by lia),
        C.model.isZero_of_isStrictlyGE a (i + 1) (by lia)⟩
    · have hib : b < i := by
        by_contra hib
        exact hmem ⟨by lia, by lia⟩
      exact ⟨C.model.isZero_of_isStrictlyLE b i hib,
        C.model.isZero_of_isStrictlyLE b (i + 1) (by lia)⟩
  letI := ModuleCat.subsingleton_of_isZero hzero.1
  letI := ModuleCat.subsingleton_of_isZero hzero.2
  have hone : C.ideal i = 1 := by
    rw [Ideal.one_eq_top]
    change fittingIdeal Γ(X, C.U)
      (HomologicalComplex.ScalarPresentation.quotient C.generator C.model i (i + 1))
      (Module.finrank Γ(X, C.U) (C.model.X (i + 1))) = ⊤
    exact fittingIdeal_eq_top_of_subsingleton Γ(X, C.U)
      (HomologicalComplex.ScalarPresentation.quotient C.generator C.model i (i + 1)) _
  exact hi hone

/-- The product ideal is the finitary product of all degreewise determinantal ideals. -/
theorem productIdeal_def {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    C.productIdeal = ∏ᶠ i : ℤ, C.ideal i := rfl

/-- The ideal-sheaf center on the affine chart obtained by transporting the product ideal to
the global sections of the restricted scheme. -/
noncomputable def productCenter {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    (C.U : X.Opens).toScheme.IdealSheafData :=
  IdealSheafData.ofIdealTop
    (Ideal.map (C.U : X.Opens).topIso.inv.hom C.productIdeal)

/-- On global sections, the chart center is the product ideal transported through
`C.U.topIso`. -/
theorem productCenter_ideal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    IdealSheafData.equivOfIsAffine C.productCenter =
      Ideal.map (C.U : X.Opens).topIso.inv.hom C.productIdeal := by
  exact IdealSheafData.equivOfIsAffine.apply_symm_apply _

end DivisorComplexChart

/-- A morphism is a good-triple modification when the divisor pullback is defined, the derived
pullback forms a good triple, and every other morphism with these properties factors uniquely
through it. -/
class IsGoodTripleModification {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (M : outParam (RingedSpace.ModuleDerived X.toRingedSpace)) (b : X' ⟶ X) : Prop where
  /-- The inverse image of the divisor along the modification is defined. -/
  pullbackDefined : D.pullbackDefined b
  /-- The pulled-back divisor and derived module form a good triple. -/
  isGoodTriple :
    IsGoodTriple (D.comap b)
      ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M)
  /-- Every morphism whose pullbacks form a good triple factors uniquely through the
  modification. -/
  lift_unique {Y : Scheme.{u}} (h : Y ⟶ X) (h_pullback : D.pullbackDefined h)
      (h_good : IsGoodTriple (D.comap h)
        ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) :
    ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h

/-- The defining conditions for a good-triple modification. -/
theorem isGoodTripleModification_iff {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (M : RingedSpace.ModuleDerived X.toRingedSpace) (b : X' ⟶ X) :
    IsGoodTripleModification D M b ↔
      D.pullbackDefined b ∧
        IsGoodTriple (D.comap b)
          ((RingedSpace.modulePullbackDerived b.toLRSHom.toShHom).obj M) ∧
        ∀ {Y : Scheme.{u}} (h : Y ⟶ X), D.pullbackDefined h →
          IsGoodTriple (D.comap h)
            ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M) →
          ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h := by
  constructor
  · intro h
    exact ⟨h.pullbackDefined, h.isGoodTriple, h.lift_unique⟩
  · rintro ⟨h_pullback, h_good, h_lift⟩
    exact ⟨h_pullback, h_good, h_lift⟩

namespace IsGoodTripleModification

/-- A good-triple modification makes the pulled-back divisor effective Cartier. -/
theorem toIsEffectiveCartierDivisor {X X' : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [h : IsGoodTripleModification D M b] :
    AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap b).subschemeι :=
  h.pullbackDefined

/-- The pulled-back divisor of a good-triple modification is canonically effective Cartier. -/
instance instIsEffectiveCartierDivisor {X X' : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [IsGoodTripleModification D M b] :
    AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap b).subschemeι :=
  toIsEffectiveCartierDivisor

/-- The universal property supplies the unique factorization of any competing good-triple
morphism. -/
theorem existsUnique_lift {X X' Y : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b : X' ⟶ X}
    [h_b : IsGoodTripleModification D M b] (h : Y ⟶ X)
    (h_pullback : D.pullbackDefined h)
    (h_good : IsGoodTriple (D.comap h)
      ((RingedSpace.modulePullbackDerived h.toLRSHom.toShHom).obj M)) :
    ExistsUnique fun c : Y ⟶ X' ↦ c ≫ b = h :=
  h_b.lift_unique h h_pullback h_good

/-- There is a unique isomorphism over the common target between two good-triple
modifications. -/
theorem existsUnique_iso {X X₁ X₂ : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} {b₁ : X₁ ⟶ X} {b₂ : X₂ ⟶ X}
    [IsGoodTripleModification D M b₁] [IsGoodTripleModification D M b₂] :
    ExistsUnique fun e : X₁ ≅ X₂ ↦ e.hom ≫ b₂ = b₁ := by
  obtain ⟨f, hf, hf_unique⟩ := existsUnique_lift (D := D) (M := M) (b := b₂) b₁
    (IsGoodTripleModification.pullbackDefined (D := D) (M := M) (b := b₁))
    (IsGoodTripleModification.isGoodTriple (D := D) (M := M) (b := b₁))
  obtain ⟨g, hg, hg_unique⟩ := existsUnique_lift (D := D) (M := M) (b := b₁) b₂
    (IsGoodTripleModification.pullbackDefined (D := D) (M := M) (b := b₂))
    (IsGoodTripleModification.isGoodTriple (D := D) (M := M) (b := b₂))
  have hfg : f ≫ g = 𝟙 X₁ := by
    obtain ⟨k, _, hk_unique⟩ := existsUnique_lift (D := D) (M := M) (b := b₁) b₁
      (IsGoodTripleModification.pullbackDefined (D := D) (M := M) (b := b₁))
      (IsGoodTripleModification.isGoodTriple (D := D) (M := M) (b := b₁))
    exact (hk_unique _ (by simp [Category.assoc, hg, hf])).trans
      (hk_unique _ (Category.id_comp b₁)).symm
  have hgf : g ≫ f = 𝟙 X₂ := by
    obtain ⟨k, _, hk_unique⟩ := existsUnique_lift (D := D) (M := M) (b := b₂) b₂
      (IsGoodTripleModification.pullbackDefined (D := D) (M := M) (b := b₂))
      (IsGoodTripleModification.isGoodTriple (D := D) (M := M) (b := b₂))
    exact (hk_unique _ (by simp [Category.assoc, hf, hg])).trans
      (hk_unique _ (Category.id_comp b₂)).symm
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro e he
  apply Iso.ext
  exact hf_unique e.hom he

/-- Restricting a good-triple modification to an affine divisor-complex chart is the blowup in
the chart's product center. -/
theorem isBlowup_restrict_affineChart {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] (C : DivisorComplexChart D M) :
    IsBlowup (b ∣_ C.U) C.productCenter := sorry

end IsGoodTripleModification

/-- An effective Cartier divisor and a perfect derived module admit a universal modification
on which their pullbacks form a good triple. -/
theorem exists_isGoodTripleModification (X : Scheme.{u}) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsGoodTripleModification D M b := sorry

namespace IsGoodTripleModification

/-- Over a quasi-compact open, a good-triple modification is an admissible blowup away from
the restricted divisor. -/
theorem isAdmissibleBlowup_restrict {X X' : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (M : RingedSpace.ModuleDerived X.toRingedSpace)
    (hM : RingedSpace.ModuleDerived.IsPerfect M) (b : X' ⟶ X)
    [IsGoodTripleModification D M b] (W : X.Opens) [QuasiCompact W.ι] :
    IsAdmissibleBlowup (D.comap W.ι).openComplement (b ∣_ W) := sorry

end IsGoodTripleModification

end AlgebraicGeometry.Scheme
