/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Lemma_10_69_4.QuotientPolynomialLocalization
import StacksCheckRecall

@[expose] public section

/-!
Source tensor and localization support for Lemma 10.69.4.

The local `Algebra` and `Module` declarations below are definitional pins to the named quotient
structures `localizedOfListQuotientAlgebra`, `localizedOfListQuotientTargetModule`, and
`localizedOfListQuotientTargetSourceModule`. Registering these presentations globally would
introduce instance diamonds.

@stack 061Q
-/

universe u v

open RingTheory
open scoped TensorProduct

-- Local declaration justification (instance diamond): the polynomial algebra action is selected
-- only for the explicit coefficient-localization maps below and is not promoted globally.
attribute [local instance] MvPolynomial.algebraMvPolynomial

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

namespace RingTheory.Sequence

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: for modules over an `R`-algebra `A`, fixing the left
factor gives the canonical `R`-linear map into the tensor product over `A`. -/
noncomputable def tensorProductBaseChangeRightMap
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y]
    (x : X) : Y →ₗ[R] X ⊗[A] Y :=
  { toFun := fun y ↦ x ⊗ₜ[A] y
    map_add' := by
      intro y₁ y₂
      -- Additivity is the right additivity relation in the tensor product over `A`.
      rw [TensorProduct.tmul_add]
    map_smul' := by
      intro r y
      -- Convert the restricted `R`-action to the `A`-action and use the tensor balancing
      -- relation to move it to the left factor.
      calc
        x ⊗ₜ[A] (r • y) = x ⊗ₜ[A] ((algebraMap R A r) • y) := by
          rw [algebraMap_smul]
        _ = ((algebraMap R A r) • x) ⊗ₜ[A] y := by
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        _ = r • (x ⊗ₜ[A] y) := by
          rw [algebraMap_smul]
          rfl }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical base-change pairing
`X → Y → X ⊗[A] Y` is `R`-bilinear. -/
noncomputable def tensorProductBaseChangeBilinear
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    X →ₗ[R] (Y →ₗ[R] X ⊗[A] Y) :=
  { toFun := fun x ↦
      tensorProductBaseChangeRightMap (R := R) (A := A) (X := X) (Y := Y) x
    map_add' := by
      intro x₁ x₂
      apply LinearMap.ext
      intro y
      -- Pointwise, this is the left additivity relation in the tensor product over `A`.
      simpa [tensorProductBaseChangeRightMap] using
        (TensorProduct.add_tmul (R := A) x₁ x₂ y)
    map_smul' := by
      intro r x
      apply LinearMap.ext
      intro y
      -- Pointwise, restricted `R`-scalars are `A`-scalars on the left tensor factor.
      dsimp [tensorProductBaseChangeRightMap]
      calc
        (r • x) ⊗ₜ[A] y = ((algebraMap R A r) • x) ⊗ₜ[A] y := by
          rw [algebraMap_smul]
        _ = r • (x ⊗ₜ[A] y) := by
          rw [algebraMap_smul, TensorProduct.smul_tmul'] }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical `R`-linear map from a tensor product over
`R` to the tensor product over an `R`-algebra `A`. -/
noncomputable def tensorProductBaseChangeMap
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    X ⊗[R] Y →ₗ[R] X ⊗[A] Y :=
  TensorProduct.lift
    (tensorProductBaseChangeBilinear (R := R) (A := A) (X := X) (Y := Y))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the base-change map sends a pure tensor over `R` to the
same pure tensor over `A`. -/
@[simp] lemma tensorProductBaseChangeMap_tmul
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y]
    (x : X) (y : Y) :
    tensorProductBaseChangeMap (R := R) (A := A) (X := X) (Y := Y) (x ⊗ₜ[R] y) =
      x ⊗ₜ[A] y := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: when `A` is a localization of `R`, the explicit
base-change map is the inverse of the canonical tensor comparison for localized modules. -/
lemma tensorProductBaseChangeMap_eq_moduleTensorEquiv_symm
    {R A X Y : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommMonoid X] [AddCommMonoid Y] [Module R X] [Module R Y]
    [Module A X] [Module A Y] [IsScalarTower R A X] [IsScalarTower R A Y] :
    tensorProductBaseChangeMap (R := R) (A := A) (X := X) (Y := Y) =
      (((IsLocalization.moduleTensorEquiv S A X Y).symm).restrictScalars R).toLinearMap := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the target quotient module used after localizing
`M / Ideal.ofList xs • ⊤`. -/
abbrev localizedOfListQuotientTarget (xs : List R) (S : Submonoid R) : Type (max u v) :=
  (LocalizedModule S M) ⧸
    (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
      Submodule (Localization S) (LocalizedModule S M))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical `R / Ideal.ofList xs`-algebra structure on
the localized quotient ring `(Localization S) / Ideal.ofList (xs.map ...)`. -/
noncomputable abbrev localizedOfListQuotientAlgebra
    (xs : List R) (S : Submonoid R) :
    Algebra (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
  let J : Ideal R := Ideal.ofList xs
  let Qloc : Type u := Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S)
  let eCoeff := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  (eCoeff.toRingHom.comp (algebraMap (R ⧸ J) Qloc)).toAlgebra

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical module structure of the localized quotient
module over the localized quotient ring. -/
noncomputable abbrev localizedOfListQuotientTargetModule
    (xs : List R) (S : Submonoid R) :
    Module ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      (localizedOfListQuotientTarget (M := M) xs S) :=
  (localized_ofList_smul_top_quotient_isTorsionBySet (M := M) xs S).module

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the target quotient module as a module over
`R / Ideal.ofList xs`, via the localized quotient ring. -/
noncomputable abbrev localizedOfListQuotientTargetSourceModule
    (xs : List R) (S : Submonoid R) :
    Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
  @Module.compHom
    ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
    (R ⧸ Ideal.ofList xs)
    (localizedOfListQuotientTarget (M := M) xs S)
    _ _ (localizedOfListQuotientTargetModule (M := M) xs S) _
    (@algebraMap (R ⧸ Ideal.ofList xs)
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
      _ _ (localizedOfListQuotientAlgebra (R := R) xs S))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient localization map preserves
addition. -/
lemma localizedOfListQuotientMap_add
    (xs : List R) (S : Submonoid R)
    (x y : M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) :
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (x + y)) =
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x) +
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) y) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: on quotient representatives, the denominator-one quotient
localization map is compatible with the transported `R / Ideal.ofList xs`-action. -/
lemma localizedOfListQuotientMap_smul_mk
    (xs : List R) (S : Submonoid R) (r : R) (m : M) :
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
          ((Ideal.Quotient.mk (Ideal.ofList xs) r : R ⧸ Ideal.ofList xs) •
            Submodule.Quotient.mk m)) =
      @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
        (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul
        (Ideal.Quotient.mk (Ideal.ofList xs) r)
        (localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (Submodule.Quotient.mk m))) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient localization map is
`R / Ideal.ofList xs`-linear. -/
lemma localizedOfListQuotientMap_smul
    (xs : List R) (S : Submonoid R) :
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    ∀ (a : R ⧸ Ideal.ofList xs)
      (x : M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)),
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
          (LocalizedModule.mkLinearMap S
            (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) (a • x)) =
        @SMul.smul (M := R ⧸ Ideal.ofList xs) (α := T)
          (localizedOfListQuotientTargetSourceModule (M := M) xs S).toSMul a
          (localized_ofList_smul_top_quotient_equiv (M := M) xs S
            (LocalizedModule.mkLinearMap S
              (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x)) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one map
`M / Ideal.ofList xs • ⊤ → (M_S) / Ideal.ofList xs_S • ⊤` as a linear map over
`R / Ideal.ofList xs`. -/
noncomputable def localizedOfListQuotientMap
    (xs : List R) (S : Submonoid R) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) →ₗ[R ⧸ Ideal.ofList xs]
      localizedOfListQuotientTarget (M := M) xs S :=
  letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
  letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
    localizedOfListQuotientTargetSourceModule (M := M) xs S
  { toFun := fun x ↦
      localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S
          (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) x)
    map_add' := localizedOfListQuotientMap_add (M := M) xs S
    map_smul' := localizedOfListQuotientMap_smul (M := M) xs S }

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient map sends a quotient
representative to the quotient class of the localized numerator. -/
lemma localizedOfListQuotientMap_mk
    (xs : List R) (S : Submonoid R) (m : M) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    localizedOfListQuotientMap (M := M) xs S (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) :
        localizedOfListQuotientTarget (M := M) xs S) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the transported `R ⧸ Ideal.ofList xs`-module structure
on the localized quotient target is compatible with the original `R`-module structure. -/
lemma localizedOfListQuotientTarget_isScalarTower
    (xs : List R) (S : Submonoid R) :
    let Q : Type u := R ⧸ Ideal.ofList xs
    let Qs : Type u :=
      (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
    IsScalarTower R Q T := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the denominator-one quotient map is a localization over
`R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListQuotientMap_isLocalizedModule
    (xs : List R) (S : Submonoid R) :
    letI : Algebra (R ⧸ Ideal.ofList xs)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
      localizedOfListQuotientAlgebra (R := R) xs S
    letI : Module
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetModule (M := M) xs S
    letI : Module (R ⧸ Ideal.ofList xs) (localizedOfListQuotientTarget (M := M) xs S) :=
      localizedOfListQuotientTargetSourceModule (M := M) xs S
    IsLocalizedModule (Algebra.algebraMapSubmonoid (R ⧸ Ideal.ofList xs) S)
      (localizedOfListQuotientMap (M := M) xs S) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the canonical renaming equivalence changes polynomial
variables from `Fin xs.length` to the length of the localized list. -/
noncomputable def localizedOfListPolynomialRenameEquiv
    (xs : List R) (S : Submonoid R) :
    MvPolynomial (Fin xs.length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) ≃ₗ[
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))]
      MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length)
        ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) :=
  (MvPolynomial.renameEquiv
    ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))
    (finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm)).toLinearEquiv

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the polynomial renaming equivalence sends monomials to
the corresponding monomials under the `List.length_map` index transport. -/
lemma localizedOfListPolynomialRenameEquiv_monomial
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) :
    localizedOfListPolynomialRenameEquiv (R := R) xs S
      (MvPolynomial.monomial e
        (1 : (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S))))) =
      MvPolynomial.monomial
        (e.mapDomain (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm))
        (1 : (Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the coefficient-localization polynomial map followed by the
canonical variable rename. -/
noncomputable def localizedOfListRenamedPolynomialMap
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    MvPolynomial (Fin xs.length) Q →ₗ[Q]
      MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs :=
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let Q : Type u := R ⧸ J
  let Qs : Type u := (Localization S) ⧸ JS
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  letI : Module Q Qs := Algebra.toModule
  let eFin : Fin xs.length ≃ Fin (xs.map (algebraMap R (Localization S))).length :=
    finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm
  let fCoeff : MvPolynomial (Fin xs.length) Q →ₐ[Q] MvPolynomial (Fin xs.length) Qs :=
    MvPolynomial.mapAlgHom (σ := Fin xs.length) (Algebra.ofId Q Qs)
  let fRename :
      MvPolynomial (Fin xs.length) Qs →ₐ[Q]
        MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs :=
    (MvPolynomial.renameEquiv Qs eFin).restrictScalars Q
  (fRename.comp fCoeff).toLinearMap

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the renamed polynomial map sends denominator-one source
monomials to the transported target monomials. -/
lemma localizedOfListRenamedPolynomialMap_monomial
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    localizedOfListRenamedPolynomialMap (R := R) xs S (MvPolynomial.monomial e (1 : Q)) =
      MvPolynomial.monomial
        (e.mapDomain (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm))
        (1 : Qs) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the renamed polynomial denominator-one map is a
localization over `R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListRenamedPolynomialMap_isLocalizedModule
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    IsLocalizedModule (Algebra.algebraMapSubmonoid Q S)
      (localizedOfListRenamedPolynomialMap (R := R) xs S) := sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized quotient ring is the localization of
`R ⧸ Ideal.ofList xs` at the image of `S`. -/
lemma localizedOfListQuotientTarget_isLocalization
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    IsLocalization (Algebra.algebraMapSubmonoid Q S) Qs := sorry

end RingTheory.Sequence

end

@[stacks 061Q "tensor base-change right map"]
#check @RingTheory.Sequence.tensorProductBaseChangeRightMap
@[stacks 061Q "tensor base-change bilinear map"]
#check @RingTheory.Sequence.tensorProductBaseChangeBilinear
@[stacks 061Q "tensor base-change map"]
#check @RingTheory.Sequence.tensorProductBaseChangeMap
@[stacks 061Q "tensor base-change map on pure tensors"]
#check @RingTheory.Sequence.tensorProductBaseChangeMap_tmul
@[stacks 061Q "tensor localization comparison"]
#check @RingTheory.Sequence.tensorProductBaseChangeMap_eq_moduleTensorEquiv_symm
@[stacks 061Q "localized quotient target"]
#check @RingTheory.Sequence.localizedOfListQuotientTarget
@[stacks 061Q "localized quotient algebra"]
#check @RingTheory.Sequence.localizedOfListQuotientAlgebra
@[stacks 061Q "localized quotient target module"]
#check @RingTheory.Sequence.localizedOfListQuotientTargetModule
@[stacks 061Q "localized quotient source module"]
#check @RingTheory.Sequence.localizedOfListQuotientTargetSourceModule
@[stacks 061Q "localized quotient map additivity"]
#check @RingTheory.Sequence.localizedOfListQuotientMap_add
@[stacks 061Q "localized quotient map on scalar representatives"]
#check @RingTheory.Sequence.localizedOfListQuotientMap_smul_mk
@[stacks 061Q "localized quotient map scalar compatibility"]
#check @RingTheory.Sequence.localizedOfListQuotientMap_smul
@[stacks 061Q "localized quotient map"]
#check @RingTheory.Sequence.localizedOfListQuotientMap
@[stacks 061Q "localized quotient map on representatives"]
#check @RingTheory.Sequence.localizedOfListQuotientMap_mk
@[stacks 061Q "localized quotient scalar tower"]
#check @RingTheory.Sequence.localizedOfListQuotientTarget_isScalarTower
@[stacks 061Q "localized quotient module owner"]
#check @RingTheory.Sequence.localizedOfListQuotientMap_isLocalizedModule
@[stacks 061Q "localized polynomial rename equivalence"]
#check @RingTheory.Sequence.localizedOfListPolynomialRenameEquiv
@[stacks 061Q "localized polynomial rename on monomials"]
#check @RingTheory.Sequence.localizedOfListPolynomialRenameEquiv_monomial
@[stacks 061Q "localized renamed polynomial map"]
#check @RingTheory.Sequence.localizedOfListRenamedPolynomialMap
@[stacks 061Q "localized renamed polynomial map on monomials"]
#check @RingTheory.Sequence.localizedOfListRenamedPolynomialMap_monomial
@[stacks 061Q "localized renamed polynomial module owner"]
#check @RingTheory.Sequence.localizedOfListRenamedPolynomialMap_isLocalizedModule
@[stacks 061Q "localized quotient ring owner"]
#check @RingTheory.Sequence.localizedOfListQuotientTarget_isLocalization
