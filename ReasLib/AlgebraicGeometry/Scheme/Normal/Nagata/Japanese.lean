/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic

@[expose] public section

/-!
# Associated-prime formulations of Japanese schemes

This module records the locally Noetherian stalkwise and unrestricted affine
associated-prime Japanese conditions, and the bridge from the affine condition
to the integral affine-local `Scheme.IsJapanese` predicate.
-/

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Transport the Japanese domain condition along a ring equivalence. -/
private theorem isN2Ring_of_ringEquiv {R : Type*} {S : Type*}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (e : R ≃+* S) [IsN2Ring R] : IsN2Ring S := by
  constructor
  intro L _ _ _ _ _
  let f : FractionRing R ≃+* FractionRing S :=
    IsFractionRing.ringEquivOfRingEquiv e
  letI : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  letI : Algebra (FractionRing R) L :=
    ((algebraMap (FractionRing S) L).comp f.toRingHom).toAlgebra
  letI : IsScalarTower R (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap S L (e r) =
        algebraMap (FractionRing S) L (f (algebraMap R (FractionRing R) r))
      rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
        ← IsScalarTower.algebraMap_apply]
  letI : Module.Finite (FractionRing R) L :=
    Module.Finite.of_equiv_equiv f.symm (RingEquiv.refl L) (by
      ext x
      simp [RingHom.algebraMap_toAlgebra])
  let c : integralClosure R L ≃+* integralClosure S L :=
    { toFun := fun x => ⟨x.1, (e.isIntegral_iff rfl x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (e.isIntegral_iff rfl x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact Module.Finite.of_equiv_equiv e c (by ext r; rfl)

private theorem integralClosure_finite_of_fractionField (R K L : Type*)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [IsN2Ring R] :
    Module.Finite R (integralClosure R L) := by
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  letI : Algebra (FractionRing R) L :=
    ((algebraMap K L).comp e.toRingHom).toAlgebra
  letI : IsScalarTower R (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R L r = algebraMap K L (e (algebraMap R (FractionRing R) r))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  letI : Module.Finite (FractionRing R) L :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext x
      simp [RingHom.algebraMap_toAlgebra])
  exact IsN2Ring.integralClosure_finite_of_finiteDimensional L

private theorem integralClosure_finite_of_localization (R S L : Type*)
    [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (M : Submonoid R) [IsLocalization M S]
    [Module.Finite R (integralClosure R L)] :
    Module.Finite S (integralClosure S L) := by
  let i : integralClosure R L →ₐ[R] (integralClosure S L).restrictScalars R :=
    Subalgebra.inclusion (fun x hx => hx.tower_top)
  letI : Algebra (integralClosure R L) (integralClosure S L) := i.toRingHom.toAlgebra
  letI : IsScalarTower R (integralClosure R L) (integralClosure S L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower (integralClosure R L) (integralClosure S L) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨m, hm, rfl⟩
      rw [IsScalarTower.algebraMap_apply R S L]
      exact (IsLocalization.map_units S ⟨m, hm⟩).map (algebraMap S L))
  letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R L) M)
      (integralClosure S L) := IsLocalization.integralClosure M
  exact Module.Finite.of_isLocalization R (integralClosure R L) M

private theorem isFractionRing_of_localization {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] :
    IsFractionRing R (FractionRing S) := by
  have hM : M ≤ nonZeroDivisors R := by
    intro m hm
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hm0
    have hu : IsUnit (algebraMap R S m) := IsLocalization.map_units S ⟨m, hm⟩
    rw [hm0, map_zero] at hu
    exact hu.ne_zero rfl
  have h : IsLocalization ((nonZeroDivisors S).comap (algebraMap R S)) (FractionRing S) :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M (nonZeroDivisors S) (FractionRing S) fun x hx => hx.mem_nonZeroDivisors
  convert h using 1
  ext r
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  exact (map_ne_zero_iff _ (IsLocalization.injective S hM)).symm

private theorem isN2Ring_of_localization {R S : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsN2Ring R] : IsN2Ring S := by
  constructor
  intro L _ _ _ _ _
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsFractionRing R (FractionRing S) := isFractionRing_of_localization M
  letI : IsScalarTower R (FractionRing S) L := IsScalarTower.to₁₃₄ R S (FractionRing S) L
  letI : Module.Finite R (integralClosure R L) :=
    integralClosure_finite_of_fractionField R (FractionRing S) L
  exact integralClosure_finite_of_localization R S L M

private theorem isN2Ring_of_principalCover {R : Type*} [CommRing R] [IsDomain R]
    (s : Finset R) (hs : Ideal.span (s : Set R) = ⊤)
    (hnz : ∀ f : s, f.1 ≠ 0)
    (hdom : ∀ f : s, IsDomain (Localization.Away f.1))
    (h : ∀ f : s, @IsN2Ring (Localization.Away f.1) _ (hdom f)) : IsN2Ring R := by
  constructor
  intro L _ _ _ _ _
  let Rₚ (f : s) := Localization.Away f.1
  letI (f : s) : IsDomain (Rₚ f) := hdom f
  letI (f : s) : IsN2Ring (Rₚ f) := h f
  have hM (f : s) : Submonoid.powers f.1 ≤ nonZeroDivisors R := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ (hnz f))
  letI (f : s) : Algebra (Rₚ f) (FractionRing R) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Rₚ f) (FractionRing R)
      (Submonoid.powers f.1) (nonZeroDivisors R) (hM f)
  letI (f : s) : IsScalarTower R (Rₚ f) (FractionRing R) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Rₚ f) (FractionRing R)
      (Submonoid.powers f.1) (nonZeroDivisors R) (hM f)
  letI (f : s) : IsFractionRing (Rₚ f) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers f.1) (Rₚ f) (FractionRing R)
  letI (f : s) : Algebra (Rₚ f) L :=
    ((algebraMap (FractionRing R) L).comp (algebraMap (Rₚ f) (FractionRing R))).toAlgebra
  letI (f : s) : IsScalarTower (Rₚ f) (FractionRing R) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI (f : s) : IsScalarTower R (Rₚ f) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R L r =
        algebraMap (FractionRing R) L
          (algebraMap (Rₚ f) (FractionRing R) (algebraMap R (Rₚ f) r))
      rw [← IsScalarTower.algebraMap_apply R (Rₚ f) (FractionRing R),
        ← IsScalarTower.algebraMap_apply R (FractionRing R) L]
  let C := integralClosure R L
  let Cₚ (f : s) := integralClosure (Rₚ f) L
  let i (f : s) : C →ₐ[R] (integralClosure (Rₚ f) L).restrictScalars R :=
    Subalgebra.inclusion (fun x hx => hx.tower_top)
  letI (f : s) : Algebra C (Cₚ f) := (i f).toRingHom.toAlgebra
  letI (f : s) : IsScalarTower R C (Cₚ f) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI (f : s) : IsScalarTower C (Cₚ f) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI (f : s) : IsLocalization
      (Algebra.algebraMapSubmonoid L (Submonoid.powers f.1)) L :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨m, hm, rfl⟩
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) L]
      exact (IsLocalization.map_units (FractionRing R) ⟨m, hM f hm⟩).map
        (algebraMap (FractionRing R) L))
  letI (f : s) : IsLocalization
      (Algebra.algebraMapSubmonoid C (Submonoid.powers f.1)) (Cₚ f) :=
    IsLocalization.integralClosure (Submonoid.powers f.1)
  exact Module.Finite.of_localizationSpan_finite' s hs
    (fun f => (IsScalarTower.toAlgHom R C (Cₚ f)).toLinearMap)
    (fun f => integralClosure_finite_of_fractionField (Rₚ f) (FractionRing R) L)


/-- A scheme satisfies the stalkwise associated-prime Japanese condition when
it is locally Noetherian and every associated-prime quotient of every stalk is
`N-2`. -/
def IsJapaneseAtStalkAssociatedPrimes (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧
    ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)),
      IsAssociatedPrime p.asIdeal (X.presheaf.stalk x) →
        IsN2Ring (X.presheaf.stalk x ⧸ p.asIdeal)

/-- A scheme satisfies the affine associated-prime Japanese condition when every
associated-prime quotient of every affine section ring is `N-2`. -/
@[stacks 033T]
def IsJapaneseAtAffineAssociatedPrimes (X : Scheme.{u}) : Prop :=
  ∀ (U : X.affineOpens) (p : PrimeSpectrum (Γ(X, U))),
    IsAssociatedPrime p.asIdeal (Γ(X, U)) →
      IsN2Ring (Γ(X, U) ⧸ p.asIdeal)

/-- The stalkwise associated-prime Japanese condition is equivalent to local
Noetherianity together with the `N-2` condition for every associated-prime
quotient of every stalk. -/
theorem isJapaneseAtStalkAssociatedPrimes_iff (X : Scheme.{u}) :
    IsJapaneseAtStalkAssociatedPrimes X ↔
      IsLocallyNoetherian X ∧
        ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)),
          IsAssociatedPrime p.asIdeal (X.presheaf.stalk x) →
            IsN2Ring (X.presheaf.stalk x ⧸ p.asIdeal) := Iff.rfl

/-- The affine associated-prime Japanese condition is equivalent to the `N-2`
condition for every associated-prime quotient of every affine section ring. -/
theorem isJapaneseAtAffineAssociatedPrimes_iff (X : Scheme.{u}) :
    IsJapaneseAtAffineAssociatedPrimes X ↔
      ∀ (U : X.affineOpens) (p : PrimeSpectrum (Γ(X, U))),
        IsAssociatedPrime p.asIdeal (Γ(X, U)) →
          IsN2Ring (Γ(X, U) ⧸ p.asIdeal) := Iff.rfl

namespace IsJapaneseAtAffineAssociatedPrimes

/-- On an integral scheme satisfying the affine associated-prime Japanese
condition, every nonempty affine open has `N-2` section ring. -/
theorem affineOpenSectionsIsN2Ring (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseAtAffineAssociatedPrimes X) (U : X.affineOpens) (hU : Nonempty U) :
    affineOpenSectionsIsN2Ring X U hU := by
  letI : Nonempty U := hU
  let R := Γ(X, U)
  have h0 : IsAssociatedPrime (⊥ : Ideal R) R := by
    refine ⟨inferInstance, 1, ?_⟩
    have hc : (⊥ : Submodule R R).colon {1} = (⊥ : Ideal R) := by
      ext r
      simp [Submodule.mem_colon_singleton]
    rw [hc]
    exact (Ideal.IsPrime.radical (inferInstance : (⊥ : Ideal R).IsPrime)).symm
  letI : IsN2Ring (R ⧸ (⊥ : Ideal R)) := hX U ⟨⊥, inferInstance⟩ h0
  exact isN2Ring_of_ringEquiv (RingEquiv.quotientBot R)

/-- An integral scheme satisfying the affine associated-prime Japanese
condition is Japanese in the affine-open sense. -/
@[stacks 033T]
theorem isJapanese (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseAtAffineAssociatedPrimes X) :
    IsJapanese X := by
  intro x
  let U : X.affineOpens :=
    ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
  exact ⟨U, X.affineCover.covers x,
    affineOpenSectionsIsN2Ring X hX U ⟨⟨x, X.affineCover.covers x⟩⟩⟩

end IsJapaneseAtAffineAssociatedPrimes

variable (X : Scheme.{u}) [IsIntegral X]

/-- An integral scheme is Japanese exactly when every nonempty affine open has
`N-2` section ring. -/
@[stacks 033V]
theorem isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∀ U : X.affineOpens,
        ∀ hU : Nonempty U,
          affineOpenSectionsIsN2Ring X U hU := by
  classical
  constructor
  · intro hX
    choose U hx hU using hX
    have hc : (⨆ x : X, (U x : X.Opens)) = ⊤ := by
      apply top_unique
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
    intro V
    apply of_affine_open_cover (P := fun W =>
      ∀ hW : Nonempty W, affineOpenSectionsIsN2Ring X W hW) U hc V
    · intro W f hW hD
      letI : Nonempty (X.basicOpen f) := hD
      have hnW : Nonempty W := by
        obtain ⟨x⟩ := hD
        exact ⟨⟨x.1, X.basicOpen_le f x.2⟩⟩
      letI : Nonempty W := hnW
      letI : IsN2Ring (Γ(X, W)) := hW hnW
      letI := W.2.isLocalization_basicOpen f
      exact isN2Ring_of_localization (R := Γ(X, W)) (S := Γ(X, X.basicOpen f))
        (Submonoid.powers f)
    · intro W s hs h hW
      letI : Nonempty W := hW
      let t := s.filter (fun f => f ≠ 0)
      have ht : Ideal.span (t : Set (Γ(X, W))) = ⊤ := by
        apply top_unique
        rw [← hs]
        apply Ideal.span_le.mpr
        intro f hf
        by_cases hf0 : f = 0
        · subst f
          exact (Ideal.span (t : Set (Γ(X, W)))).zero_mem
        · exact Ideal.subset_span (Finset.mem_filter.mpr ⟨hf, hf0⟩)
      have hnz : ∀ f : t, f.1 ≠ 0 := fun f => (Finset.mem_filter.mp f.2).2
      have hdom : ∀ f : t, IsDomain (Localization.Away f.1) := by
        intro f
        apply IsLocalization.isDomain_of_le_nonZeroDivisors
          (S := Localization.Away f.1) (M := Submonoid.powers f.1)
        rintro _ ⟨n, rfl⟩
        exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ (hnz f))
      apply isN2Ring_of_principalCover t ht hnz hdom
      intro f
      have hD : Nonempty (X.basicOpen f.1) := by
        have hne : X.basicOpen f.1 ≠ ⊥ := fun he =>
          hnz f ((basicOpen_eq_bot_iff f.1).mp he)
        obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
        exact ⟨⟨x, hx⟩⟩
      letI : Nonempty (X.basicOpen f.1) := hD
      letI : IsN2Ring (Γ(X, X.basicOpen f.1)) :=
        h ⟨f.1, (Finset.mem_filter.mp f.2).1⟩ hD
      letI : IsDomain (Localization.Away f.1) := hdom f
      letI := W.2.isLocalization_basicOpen f.1
      exact isN2Ring_of_ringEquiv
        (IsLocalization.algEquiv (Submonoid.powers f.1)
          (Γ(X, X.basicOpen f.1)) (Localization.Away f.1)).toRingEquiv
    · intro x _
      exact hU x
  · intro hX x
    let W : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
    exact ⟨W, X.affineCover.covers x, hX W ⟨⟨x, X.affineCover.covers x⟩⟩⟩

private theorem isJapanese_of_isOpenImmersion {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f] (hX : IsJapanese X) : IsJapanese Y := by
  apply (isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring Y).mpr
  intro V hV
  letI : Nonempty V := hV
  let W : X.affineOpens := ⟨f ''ᵁ (V : Y.Opens), V.2.image_of_isOpenImmersion f⟩
  have hW : Nonempty W := by
    obtain ⟨v⟩ := hV
    exact ⟨⟨f v.1, ⟨v.1, v.2, rfl⟩⟩⟩
  letI : Nonempty W := hW
  letI : IsN2Ring (Γ(X, W)) :=
    (isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring X).mp hX W hW
  exact isN2Ring_of_ringEquiv (f.appIso (V : Y.Opens)).commRingCatIsoToRingEquiv

private theorem isJapanese_of_isIso {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ X) [CategoryTheory.IsIso f] (hX : IsJapanese X) : IsJapanese Y := by
  intro y
  obtain ⟨U, hy, hU⟩ := hX (f y)
  let V : Y.affineOpens := ⟨f ⁻¹ᵁ (U : X.Opens), U.2.preimage_of_isIso f⟩
  refine ⟨V, hy, ?_⟩
  letI : Nonempty U := ⟨⟨f y, hy⟩⟩
  letI : Nonempty V := ⟨⟨y, hy⟩⟩
  letI : IsN2Ring (Γ(X, U)) := hU
  haveI : CategoryTheory.IsIso (f.app (U : X.Opens)) :=
    f.isIso_app _ (by simp [Hom.opensRange_of_isIso])
  exact isN2Ring_of_ringEquiv
    (CategoryTheory.asIso (f.app (U : X.Opens))).commRingCatIsoToRingEquiv

/-- An integral scheme is Japanese exactly when some affine open cover has
nonempty members with `N-2` section rings. The cover is indexed in the universe
of the scheme; a smaller indexing universe need not admit an affine cover. -/
@[stacks 033V]
theorem isJapanese_iff_exists_affineOpenCover_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∃ 𝒰 : Scheme.AffineOpenCover.{u, u} X,
        ∀ i : 𝒰.I₀,
          ∀ hU : Nonempty (𝒰.f i).opensRange,
            affineOpenSectionsIsN2Ring X
              ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩ hU := by
  classical
  constructor
  · intro hX
    choose U hx hU using hX
    have hc : TopologicalSpace.IsOpenCover (fun x : X => (U x : X.Opens)) := by
      apply TopologicalSpace.IsOpenCover.mk
      apply top_unique
      intro x _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
    let 𝒰 := AffineOpenCover.ofIsOpenCover (fun x : X => (U x : X.Opens)) hc
      (fun x => (U x).2)
    refine ⟨𝒰, fun i _ => ?_⟩
    dsimp only [𝒰, AffineOpenCover.ofIsOpenCover_f]
    convert hU i using 1
    apply Subtype.ext
    exact (U i).2.opensRange_fromSpec
  · rintro ⟨𝒰, h𝒰⟩ x
    exact ⟨⟨(𝒰.f (𝒰.idx x)).opensRange, isAffineOpen_opensRange _⟩,
      𝒰.covers x, h𝒰 (𝒰.idx x) ⟨⟨x, 𝒰.covers x⟩⟩⟩

/-- An integral scheme is Japanese exactly when some open cover consists of
nonempty Japanese open subschemes. -/
@[stacks 033V]
theorem isJapanese_iff_exists_openCover_by_isJapanese :
    IsJapanese X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀,
          ∀ [Nonempty (𝒰.f i).opensRange],
            IsJapanese ((𝒰.f i).opensRange).toScheme := by
  constructor
  · intro hX
    refine ⟨coverOfIsIso (P := @IsOpenImmersion) (𝟙 X), fun i hU => ?_⟩
    let U : X.Opens := Hom.opensRange (𝟙 X)
    letI : Nonempty U := hU
    have hIso : IsIso U.ι :=
      isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
        ((Opens.opensRange_ι U).trans (Hom.opensRange_of_isIso (𝟙 X)))
    exact @isJapanese_of_isIso X inferInstance U.toScheme inferInstance U.ι hIso hX
  · rintro ⟨𝒰, h𝒰⟩ x
    let U : X.Opens := (𝒰.f (𝒰.idx x)).opensRange
    have hx : x ∈ U := 𝒰.covers x
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨V, hxV, hV⟩ := h𝒰 (𝒰.idx x) ⟨x, hx⟩
    let W : X.affineOpens := ⟨U.ι ''ᵁ (V : U.toScheme.Opens),
      V.2.image_of_isOpenImmersion U.ι⟩
    have hxW : x ∈ (W : X.Opens) := ⟨⟨x, hx⟩, hxV, rfl⟩
    refine ⟨W, hxW, ?_⟩
    letI : Nonempty V := ⟨⟨⟨x, hx⟩, hxV⟩⟩
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    letI : IsN2Ring (Γ(U.toScheme, V)) := hV
    exact isN2Ring_of_ringEquiv (U.ι.appIso (V : U.toScheme.Opens)).symm.commRingCatIsoToRingEquiv

variable {X : Scheme.{u}} [IsIntegral X]

/-- A nonempty open subscheme of an integral Japanese scheme is Japanese. -/
@[stacks 033V]
theorem isJapanese_toScheme (hX : IsJapanese X) (U : X.Opens) [Nonempty U] :
    IsJapanese U.toScheme := isJapanese_of_isOpenImmersion X U.ι hX

end AlgebraicGeometry.Scheme
