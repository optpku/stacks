/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.MvPolynomial.Localization
public import ReasLib.RingTheory.Sequence.QuasiRegular.Basic
import StacksCheckRecall

/-!
Quotient and polynomial localization support for Lemma 10.69.4.
@stack 061Q
-/

@[expose] public section

universe u v

open RingTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace RingTheory.Sequence

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: an `A`-linear map that is an `R`-localization is also a
localization at the image submonoid in the intermediate algebra `A`. -/
lemma isLocalizedModule_algebraMapSubmonoid_of_restrictScalars
    {A : Type*} [CommSemiring A] [Algebra R A]
    {N₀ : Type*} [AddCommMonoid N₀] [Module A N₀] [Module R N₀] [IsScalarTower R A N₀]
    {N₁ : Type*} [AddCommMonoid N₁] [Module A N₁] [Module R N₁] [IsScalarTower R A N₁]
    {T : Submonoid R} (f : N₀ →ₗ[A] N₁)
    [IsLocalizedModule T (f.restrictScalars R)] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A T) f := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing the quotient `M / (Ideal.ofList xs) M` agrees with
quotienting the localized module by the localized ideal image. -/
noncomputable def localized_ofList_smul_top_quotient_equiv
    (xs : List R) (S : Submonoid R) :
    LocalizedModule S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) ≃ₗ[Localization S]
      ((LocalizedModule S M) ⧸
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M))) := by
  have hlocalized :
      ((Ideal.ofList xs • ⊤ : Submodule R M)).localized S =
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M)) := by
    -- Rewrite the localized submodule through the mapped list ideal before passing to quotients.
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  -- The quotient-localization owner equivalence becomes the desired textbook quotient after the
  -- explicit ideal rewrite above.
  exact (localizedQuotientEquiv S (Ideal.ofList xs • ⊤ : Submodule R M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hlocalized

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the quotient-localization comparison sends the localized class of
`m` to the class of the localized numerator. -/
lemma localized_ofList_smul_top_quotient_equiv_apply_mk
    (xs : List R) (S : Submonoid R) (m : M) :
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
      (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
        (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing the quotient ring `R / Ideal.ofList xs` at the image of
`S` agrees with quotienting `Localization S` by the mapped list ideal. -/
noncomputable def localized_ofList_quotientRing_ringEquiv
    (xs : List R) (S : Submonoid R) :
    Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.ofList xs) S) ≃+*
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := by
  let J : Ideal R := Ideal.ofList xs
  let IS : Ideal (Localization S) := Ideal.map (algebraMap R (Localization S)) J
  let eLoc :
      Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S) ≃ₐ[R ⧸ J]
        ((Localization S) ⧸ IS) :=
    Localization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ J) S) ((Localization S) ⧸ IS)
  have hIS :
      IS = Ideal.ofList (xs.map (algebraMap R (Localization S))) := by
    -- Rewrite the mapped list ideal into the literal image list ideal once and for all.
    change Ideal.map (algebraMap R (Localization S)) (Ideal.ofList xs) =
      Ideal.ofList (xs.map (algebraMap R (Localization S)))
    simpa using (Ideal.map_ofList (f := algebraMap R (Localization S)) xs)
  -- First identify the localization of `R / J`, then rewrite the target ideal to the literal
  -- localized list ideal.
  exact eLoc.toRingEquiv.trans (Ideal.quotEquivOfEq hIS)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the quotient of the localized module by the localized
`Ideal.ofList xs` action is annihilated by the localized list ideal. -/
lemma localized_ofList_smul_top_quotient_isTorsionBySet
    (xs : List R) (S : Submonoid R) :
    Module.IsTorsionBySet (Localization S)
      ((LocalizedModule S M) ⧸
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M)))
      (Ideal.ofList (xs.map (algebraMap R (Localization S)))) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: under the transported quotient-ring localization algebra,
a denominator-`1` class from `R / Ideal.ofList xs` maps to the matching class in the localized
quotient ring. -/
lemma localized_ofList_quotientRing_algebraMap_mk
    (xs : List R) (S : Submonoid R) (r : R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid Q S)
    let Qs : Type u := (Localization S) ⧸ JS
    let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
    letI : Algebra Q Qs := (eCoeff.toRingHom.comp (algebraMap Q Qloc)).toAlgebra
    algebraMap Q Qs (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk JS (algebraMap R (Localization S) r) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the transported `R / Ideal.ofList xs`-action on the
localized quotient module has the expected denominator-`1` formula on quotient representatives. -/
lemma localized_ofList_smul_top_quotient_mk_smul
    (xs : List R) (S : Submonoid R) (r : R) (y : LocalizedModule S M) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid Q S)
    let Qs : Type u := (Localization S) ⧸ JS
    let T : Type (max u v) :=
      (LocalizedModule S M) ⧸ (JS • ⊤ : Submodule (Localization S) (LocalizedModule S M))
    let htors : Module.IsTorsionBySet (Localization S) T JS :=
      localized_ofList_smul_top_quotient_isTorsionBySet (M := M) xs S
    let instQs : Module Qs T := htors.module
    let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
    let instAlg : Algebra Q Qs := (eCoeff.toRingHom.comp (algebraMap Q Qloc)).toAlgebra
    let instQ : Module Q T :=
      @Module.compHom Qs Q T _ _ instQs _ (@algebraMap Q Qs _ _ instAlg)
    letI : SMul Qs T := instQs.toSMul
    letI : Module Qs T := instQs
    letI : SMul Q T := instQ.toSMul
    letI : Module Q T := instQ
    letI : Algebra Q Qs := instAlg
    (Ideal.Quotient.mk J r : Q) • (Submodule.Quotient.mk y : T) =
      Submodule.Quotient.mk ((algebraMap R (Localization S) r) • y) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: localizing the polynomial ring over `R / Ideal.ofList xs`
at the image of `S` agrees with taking polynomials over the localized quotient ring. -/
noncomputable def localized_ofList_polynomial_ringEquiv
    (xs : List R) (S : Submonoid R) :
    Localization
        (Algebra.algebraMapSubmonoid
          (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs)) S) ≃+*
      MvPolynomial (Fin xs.length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := by
  let J : Ideal R := Ideal.ofList xs
  let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S)
  let Qs : Type u :=
    ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  letI : Algebra (R ⧸ J) Qs :=
    (eCoeff.toRingHom.comp (algebraMap (R ⧸ J) Qloc)).toAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ J) S) Qs := by
    -- Transport the quotient-ring localization structure across the canonical owner equivalence.
    exact
      (IsLocalization.isLocalization_iff_of_ringEquiv
        (M := Algebra.algebraMapSubmonoid (R ⧸ J) S)
        (S := Qloc)
        (P := Qs)
        eCoeff).mp inferInstance
  let P : Type u := MvPolynomial (Fin xs.length) (R ⧸ J)
  have hSub :
      Algebra.algebraMapSubmonoid P S =
        (Algebra.algebraMapSubmonoid (R ⧸ J) S).map
          (MvPolynomial.C (σ := Fin xs.length)) := by
    -- The polynomial denominators come entirely from coefficients, so both submonoids are the
    -- image of `S` under the same coefficient-inclusion map.
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨algebraMap R (R ⧸ J) s, ⟨s, hs, rfl⟩, ?_⟩
      simp [P, J]
    · rintro ⟨q, ⟨s, hs, hq⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [← hq]
      simp [P, J]
  let eSub :
      Localization (Algebra.algebraMapSubmonoid P S) ≃+*
        Localization
          ((Algebra.algebraMapSubmonoid (R ⧸ J) S).map
            (MvPolynomial.C (σ := Fin xs.length))) :=
    IsLocalization.ringEquivOfRingEquiv
      (M := Algebra.algebraMapSubmonoid P S)
      (T := (Algebra.algebraMapSubmonoid (R ⧸ J) S).map
        (MvPolynomial.C (σ := Fin xs.length)))
      (S := Localization (Algebra.algebraMapSubmonoid P S))
      (Q := Localization
        ((Algebra.algebraMapSubmonoid (R ⧸ J) S).map
          (MvPolynomial.C (σ := Fin xs.length))))
      (RingEquiv.refl P)
      (by simpa [hSub])
  let ePoly :
      Localization
          ((Algebra.algebraMapSubmonoid (R ⧸ J) S).map
            (MvPolynomial.C (σ := Fin xs.length))) ≃+*
        MvPolynomial (Fin xs.length) Qs :=
    (IsLocalization.algEquiv
      ((Algebra.algebraMapSubmonoid (R ⧸ J) S).map
        (MvPolynomial.C (σ := Fin xs.length)))
      (Localization
        ((Algebra.algebraMapSubmonoid (R ⧸ J) S).map
          (MvPolynomial.C (σ := Fin xs.length))))
      (MvPolynomial (Fin xs.length) Qs)).toRingEquiv
  -- First rewrite the denominator submonoid to the coefficient-image spelling, then apply the
  -- canonical polynomial-localization owner equivalence.
  exact eSub.trans ePoly

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: as an `R`-module, localizing the polynomial ring over
`R / Ideal.ofList xs` is the same as passing to polynomials over the localized quotient ring. -/
noncomputable def localized_ofList_polynomial_linearEquiv
    (xs : List R) (S : Submonoid R) :
    LocalizedModule S (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs)) ≃ₗ[R]
      MvPolynomial (Fin xs.length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := by
  let J : Ideal R := Ideal.ofList xs
  let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S)
  let Qs : Type u :=
    (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let P : Type u := MvPolynomial (Fin xs.length) (R ⧸ J)
  let P' : Type u := MvPolynomial (Fin xs.length) Qs
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  letI : Algebra (R ⧸ J) Qs :=
    (eCoeff.toRingHom.comp (algebraMap (R ⧸ J) Qloc)).toAlgebra
  haveI : IsScalarTower R (R ⧸ J) Qs :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      let IS : Ideal (Localization S) := Ideal.map (algebraMap R (Localization S)) J
      have hIS : IS = Ideal.ofList (xs.map (algebraMap R (Localization S))) := by
        change Ideal.map (algebraMap R (Localization S)) (Ideal.ofList xs) =
          Ideal.ofList (xs.map (algebraMap R (Localization S)))
        simpa using (Ideal.map_ofList (f := algebraMap R (Localization S)) xs)
      -- Evaluate the transported coefficient-ring localization on a denominator-`1` class.
      change Ideal.Quotient.mk _ ((algebraMap R (Localization S)) r) =
        Ideal.quotEquivOfEq hIS
          ((Localization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ J) S) ((Localization S) ⧸ IS))
            ((algebraMap (R ⧸ J) Qloc) ((Ideal.Quotient.mk J) r)))
      symm
      exact
        congrArg (Ideal.quotEquivOfEq hIS)
          ((Localization.algEquiv
              (Algebra.algebraMapSubmonoid (R ⧸ J) S)
              ((Localization S) ⧸ IS)).commutes
            ((Ideal.Quotient.mk J) r))
  let fCoeff : (R ⧸ J) →ₐ[R] Qs := IsScalarTower.toAlgHom R (R ⧸ J) Qs
  letI : Algebra P P' := (MvPolynomial.mapAlgHom (σ := Fin xs.length) fCoeff).toAlgebra
  letI : Module P P' := Algebra.toModule
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ J) S) Qs := by
    -- First realize the localized quotient ring as the canonical localization owner for the
    -- coefficient ring `R / Ideal.ofList xs`.
    exact
      (IsLocalization.isLocalization_iff_of_ringEquiv
        (M := Algebra.algebraMapSubmonoid (R ⧸ J) S)
        (S := Qloc)
        (P := Qs)
        eCoeff).mp inferInstance
  have hSub :
      Algebra.algebraMapSubmonoid P S =
        (Algebra.algebraMapSubmonoid (R ⧸ J) S).map
          (MvPolynomial.C (σ := Fin xs.length)) := by
    -- Polynomial denominators come only from coefficients, so the localization submonoid is the
    -- coefficient-image submonoid.
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨algebraMap R (R ⧸ J) s, ⟨s, hs, rfl⟩, ?_⟩
      simp [P, J]
    · rintro ⟨q, ⟨s, hs, hq⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [← hq]
      simp [P, J]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid P S) P' := by
    -- Once the coefficient ring is localized canonically, the multivariable polynomial ring is
    -- localized by the induced coefficient-image submonoid.
    rw [hSub]
    exact MvPolynomial.isLocalization (σ := Fin xs.length)
      (M := Algebra.algebraMapSubmonoid (R ⧸ J) S) Qs
  let f : P →ₗ[R] P' := IsScalarTower.toAlgHom R P P'
  have hf : IsLocalizedModule S f := by
    -- Reinterpret the localized polynomial ring as an `S`-localization after forgetting the
    -- intermediate coefficient-ring structure.
    change IsLocalizedModule S (IsScalarTower.toAlgHom R P P').toLinearMap
    infer_instance
  -- Package the transported localization owner into the desired `R`-linear equivalence.
  exact IsLocalizedModule.iso S f

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the polynomial localization equivalence sends the localized
denominator-`1` monomial to the matching monomial over the localized quotient ring. -/
lemma localized_ofList_polynomial_linearEquiv_apply_mk_monomial
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) :
    localized_ofList_polynomial_linearEquiv (R := R) xs S
        (LocalizedModule.mkLinearMap S
          (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
          (MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList xs))) =
      MvPolynomial.monomial e
        (1 : (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: a localization over an algebra remains a localization after
restricting scalars to the base ring and pulling the denominator back along the algebra map. -/
lemma isLocalizedModule_restrictScalars_of_algebraMapSubmonoid
    {A : Type*} [CommSemiring A] [Algebra R A]
    {N₀ : Type*} [AddCommMonoid N₀] [Module A N₀] [Module R N₀] [IsScalarTower R A N₀]
    {N₁ : Type*} [AddCommMonoid N₁] [Module A N₁] [Module R N₁] [IsScalarTower R A N₁]
    {T : Submonoid R} (f : N₀ →ₗ[A] N₁)
    [IsLocalizedModule (Algebra.algebraMapSubmonoid A T) f] :
    IsLocalizedModule T (f.restrictScalars R) := sorry


end RingTheory.Sequence

end

@[stacks 061Q "localized quotient module equivalence"]
#check @RingTheory.Sequence.localized_ofList_smul_top_quotient_equiv
@[stacks 061Q "localized module quotient action"]
#check @RingTheory.Sequence.localized_ofList_smul_top_quotient_equiv_apply_mk
@[stacks 061Q "localized quotient torsion"]
#check @RingTheory.Sequence.localized_ofList_smul_top_quotient_isTorsionBySet
@[stacks 061Q "localized quotient ring equivalence"]
#check @RingTheory.Sequence.localized_ofList_quotientRing_ringEquiv
@[stacks 061Q "localized quotient coefficient map"]
#check @RingTheory.Sequence.localized_ofList_quotientRing_algebraMap_mk
@[stacks 061Q "localized quotient scalar action"]
#check @RingTheory.Sequence.localized_ofList_smul_top_quotient_mk_smul
@[stacks 061Q "localized polynomial ring equivalence"]
#check @RingTheory.Sequence.localized_ofList_polynomial_ringEquiv
@[stacks 061Q "localized polynomial module equivalence"]
#check @RingTheory.Sequence.localized_ofList_polynomial_linearEquiv
@[stacks 061Q "localized polynomial monomial map"]
#check @RingTheory.Sequence.localized_ofList_polynomial_linearEquiv_apply_mk_monomial
@[stacks 061Q "algebra localization restriction"]
#check @RingTheory.Sequence.isLocalizedModule_algebraMapSubmonoid_of_restrictScalars
@[stacks 061Q "localization scalar restriction"]
#check @RingTheory.Sequence.isLocalizedModule_restrictScalars_of_algebraMapSubmonoid
