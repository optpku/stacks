/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra

/-!
# Localization functor of ring deformation categories

A multiplicative subset `S ⊆ P` induces a functor
`deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S)`
sending a deformation `(A, Q) → (k, P)` to `(A, S_Q⁻¹ Q) → (k, S⁻¹ P)`,
where `S_Q` is the inverse image of `S` in `Q`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

/-- The underlying ring map `Q →+* P` of a morphism `(A, Q) ⟶ (k, P)`. -/
def residueRingHom {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    Q.algebra →+* P :=
  f.toRingHom

/-- `residueRingHom` is the stored ring map of a morphism to `ofResidue P`. -/
theorem residueRingHom_apply {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P)
    (x : Q.algebra) : residueRingHom f x = f.toRingHom x :=
  rfl

/-- Inverse image `S_Q ⊆ Q` of a multiplicative subset `S ⊆ P` along a morphism
`(A, Q) ⟶ (k, P)` in `FlatAlgebraCat`. -/
abbrev preimageSubmonoid (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) : Submonoid Q.algebra :=
  S.comap (residueRingHom f)

/-- Membership in `preimageSubmonoid` is inverse-image membership along `toRingHom`. -/
theorem preimageSubmonoid_mem (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ preimageSubmonoid S f ↔ f.toRingHom x ∈ S :=
  Iff.rfl

/-- A morphism of deformations carries inverse-image denominators to denominators. -/
private theorem localization_preimage_le (S : Submonoid P)
    {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    preimageSubmonoid S X.hom ≤ (preimageSubmonoid S Y.hom).comap f.left.toRingHom := by
  intro x hx
  change X.hom.toRingHom x ∈ S at hx
  change Y.hom.toRingHom (f.left.toRingHom x) ∈ S
  have h := congrArg (fun h : X.left ⟶ ofResidue Λ k P ↦ h.toRingHom x) (Over.w f)
  change Y.hom.toRingHom (f.left.toRingHom x) = X.hom.toRingHom x at h
  rwa [h]

/-- Residue compatibility makes every arrow to the residue base surjective. -/
private theorem localization_base_surjective (A : ArtinianLocalAlgCat Λ k) (f : A ⟶ ArtinianLocalAlgCat.residue Λ k) :
    Function.Surjective f.hom := by
  intro y
  obtain ⟨r, hr⟩ := A.residueFieldIso.surjective y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  refine ⟨a, ?_⟩
  have hc := AlgHom.congr_fun (ArtinianLocalAlgCat.Hom.residue_compat f)
    (IsLocalRing.residue A.carrier a)
  change (ArtinianLocalAlgCat.residue Λ k).residueFieldIso
    (IsLocalRing.ResidueField.mapAlgHom f.hom (IsLocalRing.residue A.carrier a)) = _ at hc
  rw [IsLocalRing.ResidueField.mapAlgHom_residue] at hc
  exact hc.trans hr

section
variable {A B Q R : Type*} [CommRing A] [CommRing B] [CommRing Q] [CommRing R]
  [Algebra A B] [Algebra A Q] [Algebra A R] [Algebra B R] [Algebra Q R]
  [IsScalarTower A B R] [IsScalarTower A Q R] [Algebra.IsPushout A B Q R]

/-- A surjective leg of an algebra pushout has the extended kernel. -/
private theorem localization_pushout_ker (hf : Function.Surjective (algebraMap A B)) :
    RingHom.ker (algebraMap Q R) = (RingHom.ker (algebraMap A B)).map (algebraMap A Q) := by
  haveI : Algebra.IsPushout A Q B R := Algebra.IsPushout.symm inferInstance
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Q (RingHom.ker (algebraMap A B))).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Q ≃ₐ[Q] Q)
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hf)).trans
        (Algebra.IsPushout.equiv A Q B R))
  ext q
  change algebraMap Q R q = 0 ↔ _
  rw [← e.commutes q, ← map_zero e, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Nilpotence of a surjective kernel persists under algebra base change. -/
private theorem localization_pushout_nilpotent (hf : Function.Surjective (algebraMap A B))
    (hn : IsNilpotent (RingHom.ker (algebraMap A B)))
    {q : Q} (hq : algebraMap Q R q = 0) : IsNilpotent q := by
  have hq' : q ∈ (RingHom.ker (algebraMap A B)).map (algebraMap A Q) := by
    rw [← localization_pushout_ker (R := R) hf]
    exact hq
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  simpa only [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot]
    using Ideal.pow_mem_pow hq' n
end

/-- Elements killed by the special-fibre map are nilpotent. -/
private theorem localization_residue_nilpotent
    (X : deformationCategory Λ k P) {q : X.left.algebra}
    (hq : residueRingHom X.hom q = 0) : IsNilpotent q := by
  letI : Algebra X.left.base.carrier k := algebraAlong X.hom.baseHom
  letI : Algebra X.left.base.carrier P := compAlgebraAlong X.hom.baseHom
  letI : IsScalarTower X.left.base.carrier k P :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra X.left.algebra P := (residueRingHom X.hom).toAlgebra
  letI : IsScalarTower X.left.base.carrier X.left.algebra P :=
    IsScalarTower.of_algebraMap_eq' X.hom.commutes.symm
  haveI : Algebra.IsPushout X.left.base.carrier k X.left.algebra P :=
    ⟨X.hom.isIso_tensor⟩
  have hk : RingHom.ker (algebraMap X.left.base.carrier k) =
      IsLocalRing.maximalIdeal X.left.base.carrier := by
    let b : X.left.base.carrier →+* k := X.hom.baseHom.hom.toRingHom
    letI : IsLocalHom b := ⟨fun a ha ↦ X.hom.baseHom.isLocalHom.map_nonunit a ha⟩
    change RingHom.ker b = _
    rw [← IsLocalRing.maximalIdeal_comap b, IsLocalRing.maximalIdeal_eq_bot]
    rfl
  apply localization_pushout_nilpotent (A := X.left.base.carrier) (B := k) (R := P)
    (localization_base_surjective X.left.base X.hom.baseHom)
  · rw [hk]
    exact (isArtinianRing_iff_isNilpotent_maximalIdeal X.left.base.carrier).mp inferInstance
  · exact hq

/-- The special-fibre ring map of a deformation is surjective. -/
private theorem localization_residue_surjective
    (X : deformationCategory Λ k P) : Function.Surjective (residueRingHom X.hom) := by
  letI : Algebra X.left.base.carrier k := algebraAlong X.hom.baseHom
  letI : Algebra X.left.base.carrier P := compAlgebraAlong X.hom.baseHom
  letI : IsScalarTower X.left.base.carrier k P :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra X.left.algebra P := (residueRingHom X.hom).toAlgebra
  letI : IsScalarTower X.left.base.carrier X.left.algebra P :=
    IsScalarTower.of_algebraMap_eq' X.hom.commutes.symm
  haveI : Algebra.IsPushout X.left.base.carrier k X.left.algebra P :=
    ⟨X.hom.isIso_tensor⟩
  have hf : Function.Surjective (algebraMap X.left.base.carrier k) :=
    localization_base_surjective X.left.base X.hom.baseHom
  change Function.Surjective (algebraMap X.left.algebra P)
  intro p
  obtain ⟨z, hz⟩ := (Algebra.IsPushout.equiv X.left.base.carrier k X.left.algebra P).surjective p
  obtain ⟨q, hq⟩ := TensorProduct.mk_surjective (R := X.left.base.carrier) (S := k)
    (M := X.left.algebra) hf z
  rw [← hq] at hz
  refine ⟨q, ?_⟩
  have ht := Algebra.IsPushout.equiv_tmul X.left.base.carrier k X.left.algebra P (1 : k) q
  rw [map_one, one_mul] at ht
  exact ht.symm.trans hz

/-- Localizing target denominators agrees with localizing the images of source denominators. -/
private theorem localization_image_isLocalization
    (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    IsLocalization ((preimageSubmonoid S X.hom).map f.left.toRingHom)
      (Localization (preimageSubmonoid S Y.hom)) := by
  let T := (preimageSubmonoid S X.hom).map f.left.toRingHom
  let U := preimageSubmonoid S Y.hom
  have hTU : T ≤ U := by
    rintro y ⟨q, hq, rfl⟩
    exact localization_preimage_le S f hq
  have hU : ∀ y ∈ U, IsUnit (algebraMap Y.left.algebra (Localization T) y) := by
    intro y hy
    obtain ⟨q, hq⟩ := localization_residue_surjective X (residueRingHom Y.hom y)
    have hqS : q ∈ preimageSubmonoid S X.hom := by
      change residueRingHom X.hom q ∈ S
      rw [hq]
      exact hy
    have hc := congrArg (fun h : X.left ⟶ ofResidue Λ k P ↦ h.toRingHom q) (Over.w f)
    change residueRingHom Y.hom (f.left.toRingHom q) = residueRingHom X.hom q at hc
    have hn : IsNilpotent (y - f.left.toRingHom q) :=
      localization_residue_nilpotent Y (by rw [_root_.map_sub, hc, hq, sub_self])
    have hu := IsLocalization.map_units (Localization T)
      (⟨f.left.toRingHom q, ⟨q, hqS, rfl⟩⟩ : T)
    have hunit := (hn.map (algebraMap Y.left.algebra (Localization T))).isUnit_add_right_of_commute
      hu (Commute.all _ _)
    simpa only [← _root_.map_add, sub_add_cancel] using hunit
  haveI : IsLocalization U (Localization T) := IsLocalization.of_le T U hTU hU
  exact (IsLocalization.isLocalization_iff_of_isLocalization T U (Localization T)).mpr inferInstance

/-- Localization of a flat algebra is flat over its base. -/
private theorem localizeObj_flat (S : Submonoid P) (X : deformationCategory Λ k P) :
    Module.Flat X.left.base.carrier (Localization (preimageSubmonoid S X.hom)) := by
  infer_instance

/-- The localized pair `(A, S_Q⁻¹ Q)` of a deformation of `P`. -/
def localizeObj (S : Submonoid P) (X : deformationCategory Λ k P) : FlatAlgebraCat Λ k :=
  of X.left.base (Localization (preimageSubmonoid S X.hom))
    (isFlat := by exact localizeObj_flat S X)

/-- `localizeObj` keeps the Artinian base of the original deformation. -/
theorem localizeObj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).base = X.left.base :=
  rfl

/-- The algebra of `localizeObj S X` is the localization of `Q` at `S_Q`. -/
theorem localizeObj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).algebra = Localization (preimageSubmonoid S X.hom) :=
  rfl

/-- The localization map commutes with the base algebra maps. -/
private theorem localizeHom_commutes (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S)).comp (algebraMap (localizeObj S X).base.carrier (localizeObj S X).algebra) =
      (algebraMap (ofResidue Λ k (Localization S)).base.carrier (ofResidue Λ k (Localization S)).algebra).comp (X.hom.baseHom).hom.toRingHom := by
  apply RingHom.ext
  intro r
  change IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
      (Localization S) (T := S) (residueRingHom X.hom) le_rfl
      (algebraMap X.left.algebra (Localization (preimageSubmonoid S X.hom))
        (algebraMap X.left.base.carrier X.left.algebra r)) =
    algebraMap P (Localization S) (algebraMap k P (X.hom.baseHom.hom r))
  rw [IsLocalization.map_eq]
  exact congrArg (algebraMap P (Localization S)) (RingHom.congr_fun X.hom.commutes r)

/-- The canonical tensor lift of the localization map is bijective. -/
private theorem localizeHom_isIsoTensor (S : Submonoid P) (X : deformationCategory Λ k P) :
    Function.Bijective (canonicalTensorMap
      (Q := localizeObj S X) (P := ofResidue Λ k (Localization S))
      (X.hom.baseHom) ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S)) (localizeHom_commutes S X)) := by
  letI : Algebra X.left.base.carrier k := algebraAlong X.hom.baseHom
  letI : Algebra X.left.base.carrier P := compAlgebraAlong X.hom.baseHom
  letI : IsScalarTower X.left.base.carrier k P :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra X.left.algebra P := (residueRingHom X.hom).toAlgebra
  letI : IsScalarTower X.left.base.carrier X.left.algebra P :=
    IsScalarTower.of_algebraMap_eq' X.hom.commutes.symm
  haveI : Algebra.IsPushout X.left.base.carrier k X.left.algebra P :=
    ⟨X.hom.isIso_tensor⟩
  have hg : Function.Surjective (algebraMap X.left.algebra P) := by
    change Function.Surjective (residueRingHom X.hom)
    exact localization_residue_surjective X
  haveI : IsLocalization
      ((preimageSubmonoid S X.hom).map (algebraMap X.left.algebra P)) (Localization S) := by
    have hmap : (preimageSubmonoid S X.hom).map (algebraMap X.left.algebra P) = S :=
      Submonoid.map_comap_eq_self_of_surjective hg
    rw [hmap]
    infer_instance
  letI : Algebra (Localization (preimageSubmonoid S X.hom)) (Localization S) :=
    (IsLocalization.map (M := preimageSubmonoid S X.hom)
      (T := S) (S := Localization (preimageSubmonoid S X.hom))
      (Localization S) (residueRingHom X.hom) le_rfl).toAlgebra
  haveI : IsScalarTower X.left.algebra
      (Localization (preimageSubmonoid S X.hom)) (Localization S) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.map_comp (M := preimageSubmonoid S X.hom)
      (T := S) (S := Localization (preimageSubmonoid S X.hom)) (Q := Localization S)
      (g := residueRingHom X.hom) le_rfl).symm
  haveI : IsScalarTower X.left.base.carrier
      (Localization (preimageSubmonoid S X.hom)) (Localization S) :=
    IsScalarTower.to₁₃₄ X.left.base.carrier X.left.algebra _ _
  haveI : Algebra.IsPushout X.left.base.carrier X.left.algebra k P :=
    Algebra.IsPushout.symm inferInstance
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid P (preimageSubmonoid S X.hom)) (Localization S) :=
    ‹IsLocalization ((preimageSubmonoid S X.hom).map (algebraMap X.left.algebra P))
      (Localization S)›
  haveI : Algebra.IsPushout X.left.algebra P
      (Localization (preimageSubmonoid S X.hom)) (Localization S) :=
    Algebra.isPushout_of_isLocalization (preimageSubmonoid S X.hom)
      (Localization (preimageSubmonoid S X.hom)) P (Localization S)
  haveI : Algebra.IsPushout X.left.base.carrier k
      (Localization (preimageSubmonoid S X.hom)) (Localization S) :=
    ((Algebra.IsPushout.comp_iff X.left.base.carrier X.left.algebra k P).mpr
      (Algebra.IsPushout.symm inferInstance)).symm
  exact (inferInstance : Algebra.IsPushout X.left.base.carrier k
    (Localization (preimageSubmonoid S X.hom)) (Localization S)).out

/-- The morphism `(A, S_Q⁻¹ Q) ⟶ (k, S⁻¹ P)` induced by localization. -/
noncomputable def localizeHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    localizeObj S X ⟶ ofResidue Λ k (Localization S) :=
  Hom.of (X.hom.baseHom) ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S))
    (by exact localizeHom_commutes S X) (by exact localizeHom_isIsoTensor S X)

/-- `localizeHom` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeHom_baseHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeHom S X).baseHom = X.hom.baseHom :=
  rfl

/-- The localization map commutes with the base algebra maps. -/
private theorem localizeMap_commutes (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom))).comp (algebraMap (localizeObj S X).base.carrier (localizeObj S X).algebra) =
      (algebraMap (localizeObj S Y).base.carrier (localizeObj S Y).algebra).comp (f.left.baseHom).hom.toRingHom := by
  apply RingHom.ext
  intro r
  change IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) (T := preimageSubmonoid S Y.hom)
          f.left.toRingHom (localization_preimage_le S f)
      (algebraMap X.left.algebra (Localization (preimageSubmonoid S X.hom))
        (algebraMap X.left.base.carrier X.left.algebra r)) =
    algebraMap Y.left.algebra (Localization (preimageSubmonoid S Y.hom))
      (algebraMap Y.left.base.carrier Y.left.algebra (f.left.baseHom.hom r))
  rw [IsLocalization.map_eq]
  exact congrArg (algebraMap Y.left.algebra (Localization (preimageSubmonoid S Y.hom)))
    (RingHom.congr_fun f.left.commutes r)

/-- The canonical tensor lift of the localization map is bijective. -/
private theorem localizeMap_isIsoTensor (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    Function.Bijective (canonicalTensorMap
      (Q := localizeObj S X) (P := localizeObj S Y)
      (f.left.baseHom) ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom))) (localizeMap_commutes S f)) := by
  letI : Algebra X.left.base.carrier Y.left.base.carrier := algebraAlong f.left.baseHom
  letI : Algebra X.left.base.carrier Y.left.algebra := compAlgebraAlong f.left.baseHom
  letI : IsScalarTower X.left.base.carrier Y.left.base.carrier Y.left.algebra :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra X.left.algebra Y.left.algebra := f.left.toRingHom.toAlgebra
  letI : IsScalarTower X.left.base.carrier X.left.algebra Y.left.algebra :=
    IsScalarTower.of_algebraMap_eq' f.left.commutes.symm
  haveI : Algebra.IsPushout X.left.base.carrier Y.left.base.carrier X.left.algebra Y.left.algebra :=
    ⟨f.left.isIso_tensor⟩
  haveI : IsLocalization
      (Algebra.algebraMapSubmonoid Y.left.algebra (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) := localization_image_isLocalization S f
  letI : Algebra (Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) :=
    (IsLocalization.map (M := preimageSubmonoid S X.hom)
      (T := preimageSubmonoid S Y.hom) (S := Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom (localization_preimage_le S f)).toAlgebra
  haveI : IsScalarTower X.left.algebra (Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (M := preimageSubmonoid S X.hom)
        (T := preimageSubmonoid S Y.hom) (S := Localization (preimageSubmonoid S X.hom))
        (Q := Localization (preimageSubmonoid S Y.hom))
        (g := f.left.toRingHom) (localization_preimage_le S f)).symm
  haveI : IsScalarTower X.left.base.carrier (Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S Y.hom)) :=
    IsScalarTower.to₁₃₄ X.left.base.carrier X.left.algebra _ _
  haveI : Algebra.IsPushout X.left.base.carrier X.left.algebra Y.left.base.carrier Y.left.algebra :=
    Algebra.IsPushout.symm inferInstance
  haveI : Algebra.IsPushout X.left.algebra Y.left.algebra
      (Localization (preimageSubmonoid S X.hom)) (Localization (preimageSubmonoid S Y.hom)) :=
    Algebra.isPushout_of_isLocalization (preimageSubmonoid S X.hom)
      (Localization (preimageSubmonoid S X.hom)) Y.left.algebra
      (Localization (preimageSubmonoid S Y.hom))
  haveI : Algebra.IsPushout X.left.base.carrier Y.left.base.carrier
      (Localization (preimageSubmonoid S X.hom)) (Localization (preimageSubmonoid S Y.hom)) :=
    ((Algebra.IsPushout.comp_iff X.left.base.carrier X.left.algebra
      Y.left.base.carrier Y.left.algebra).mpr (Algebra.IsPushout.symm inferInstance)).symm
  exact (inferInstance : Algebra.IsPushout X.left.base.carrier Y.left.base.carrier
    (Localization (preimageSubmonoid S X.hom)) (Localization (preimageSubmonoid S Y.hom))).out

/-- The morphism of localized pairs induced by a morphism of deformations. -/
noncomputable def localizeMap (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    localizeObj S X ⟶ localizeObj S Y :=
  Hom.of (f.left.baseHom) ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom)))
    (by exact localizeMap_commutes S f) (by exact localizeMap_isIsoTensor S f)

/-- `localizeMap` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeMap_baseHom (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    (localizeMap S f).baseHom = f.left.baseHom :=
  rfl

/-- Equality of the stored base and ring maps determines a flat-algebra morphism. -/
private theorem localization_hom_ext {Q R : FlatAlgebraCat Λ k} {f g : Q ⟶ R}
    (hb : f.baseHom = g.baseHom) (hr : f.toRingHom = g.toRingHom) : f = g := by
  rcases f with ⟨fb, fr, fc, fi⟩
  rcases g with ⟨gb, gr, gc, gi⟩
  change fb = gb at hb
  change fr = gr at hr
  subst gb
  subst gr
  rfl

/-- Localized maps commute with the maps to the localized residue algebra. -/
private theorem localizeMap_w (S : Submonoid P) {X Y : deformationCategory Λ k P}
    (f : X ⟶ Y) : localizeMap S f ≫ localizeHom S Y = localizeHom S X := by
  apply localization_hom_ext
  · change f.left.baseHom ≫ Y.hom.baseHom = X.hom.baseHom
    exact congrArg Hom.baseHom (Over.w f)
  · change (IsLocalization.map (M := preimageSubmonoid S Y.hom)
        (S := Localization (preimageSubmonoid S Y.hom))
        (Localization S) (T := S) (residueRingHom Y.hom) le_rfl).comp
        (IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
          (Localization (preimageSubmonoid S Y.hom)) (T := preimageSubmonoid S Y.hom)
          f.left.toRingHom (localization_preimage_le S f)) =
      IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
        (Localization S) (T := S) (residueRingHom X.hom) le_rfl
    apply IsLocalization.ringHom_ext (preimageSubmonoid S X.hom)
    ext x
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    exact congrArg (algebraMap P (Localization S))
      (congrArg (fun h : X.left ⟶ ofResidue Λ k P ↦ h.toRingHom x) (Over.w f))

/-- Localization preserves identity maps of deformations. -/
private theorem localizeMap_id (S : Submonoid P) (X : deformationCategory Λ k P) :
    localizeMap S (𝟙 X) = 𝟙 (localizeObj S X) := by
  apply localization_hom_ext
  · rfl
  · change IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
      (Localization (preimageSubmonoid S X.hom)) (T := preimageSubmonoid S X.hom)
        (RingHom.id X.left.algebra) le_rfl = RingHom.id _
    ext x
    exact IsLocalization.map_id x _

/-- Localization preserves composites of deformation maps. -/
private theorem localizeMap_comp (S : Submonoid P) {X Y Z : deformationCategory Λ k P}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    localizeMap S (f ≫ g) = localizeMap S f ≫ localizeMap S g := by
  apply localization_hom_ext
  · rfl
  · change IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
        (Localization (preimageSubmonoid S Z.hom)) (T := preimageSubmonoid S Z.hom)
          (g.left.toRingHom.comp f.left.toRingHom) (localization_preimage_le S (f ≫ g)) =
      (IsLocalization.map (M := preimageSubmonoid S Y.hom)
        (S := Localization (preimageSubmonoid S Y.hom))
        (Localization (preimageSubmonoid S Z.hom)) (T := preimageSubmonoid S Z.hom)
          g.left.toRingHom (localization_preimage_le S g)).comp
        (IsLocalization.map (M := preimageSubmonoid S X.hom)
        (S := Localization (preimageSubmonoid S X.hom))
          (Localization (preimageSubmonoid S Y.hom)) (T := preimageSubmonoid S Y.hom)
          f.left.toRingHom (localization_preimage_le S f))
    apply IsLocalization.ringHom_ext (preimageSubmonoid S X.hom)
    ext x
    simp only [RingHom.comp_apply, IsLocalization.map_eq]

/-- The functor `Def_P ⥤ Def_{S⁻¹ P}` sending a deformation of `P` to its localization at `S`. -/
noncomputable def localizationFunctor (S : Submonoid P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S) where
  obj X := Over.mk (localizeHom S X)
  map f := Over.homMk (localizeMap S f) (by exact localizeMap_w S f)
  map_id X := by
    apply Over.OverMorphism.ext
    exact localizeMap_id S X
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact localizeMap_comp S f g

/-- The localized deformation has the same Artinian base. -/
theorem localizationFunctor_obj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.base = X.left.base :=
  rfl

/-- The localized deformation has algebra `S_Q⁻¹ Q`. -/
theorem localizationFunctor_obj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.algebra =
      Localization (preimageSubmonoid S X.hom) :=
  rfl

/-- `localizationFunctor` lies over `C_Λ`: it commutes with the projections to
`ArtinianLocalAlgCat`. -/
theorem localizationFunctor_comp_forget (S : Submonoid P) :
    localizationFunctor S ⋙
        Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k (Localization S))) ⋙ forget =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget :=
  rfl

section

variable (Λ k)

/-- The localization functor as a morphism of categories over `C_Λ`. -/
noncomputable def localizationBasedFunctor (S : Submonoid P) :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k (Localization S))) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) where
  toFunctor := localizationFunctor S
  w := localizationFunctor_comp_forget S

/-- The underlying functor of `localizationBasedFunctor` is `localizationFunctor`. -/
theorem localizationBasedFunctor_toFunctor (S : Submonoid P) :
    (localizationBasedFunctor Λ k S).toFunctor = localizationFunctor S :=
  rfl

end

end FlatAlgebraCat
