/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import ReasLib.RingTheory.RingHom.IndZariski

@[expose] public section

/-!
# Ind-(Zariski localization) ring homomorphisms

An ind-(Zariski localization) ring homomorphism is a filtered colimit of finite
products of principal localizations. The finite-stage property is expressed on
algebras and on morphisms of commutative rings, and implies the local-isomorphism
property. Consequently, every ind-(Zariski localization) is ind-Zariski.
-/

open CategoryTheory MorphismProperty RingHom

universe u v w

namespace Algebra

/-- An `R`-algebra is a finite product of principal localizations if it is
`R`-algebra equivalent to `Π i : Fin n, Localization.Away (f i)` for some
family `f : Fin n → R`. -/
def IsFiniteProductOfPrincipalLocalizations (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : Prop :=
  ∃ (n : ℕ) (f : Fin n → R),
    Nonempty (((i : Fin n) → Localization.Away (f i)) ≃ₐ[R] S)

namespace IsFiniteProductOfPrincipalLocalizations

/-- An algebra is a finite product of principal localizations if and only if it
is equivalent to a finite product of `Localization.Away` algebras. -/
theorem iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    IsFiniteProductOfPrincipalLocalizations R S ↔
      ∃ (n : ℕ) (f : Fin n → R),
        Nonempty (((i : Fin n) → Localization.Away (f i)) ≃ₐ[R] S) :=
  Iff.rfl

/-- A principal localization is a one-factor finite product of principal
localizations. -/
theorem of_localizationAway {R : Type u} [CommRing R] (r : R) :
    IsFiniteProductOfPrincipalLocalizations R (Localization.Away r) := by
  exact ⟨1, fun _ ↦ r, ⟨AlgEquiv.funUnique R (Fin 1) (Localization.Away r)⟩⟩

/-- A standard open immersion is a finite product of principal localizations. -/
theorem of_isStandardOpenImmersion {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsStandardOpenImmersion R S] :
    IsFiniteProductOfPrincipalLocalizations R S := by
  obtain ⟨r, hr⟩ := IsStandardOpenImmersion.exists_away R S
  letI := hr
  exact ⟨1, fun _ ↦ r,
    ⟨(AlgEquiv.funUnique R (Fin 1) (Localization.Away r)).trans
      (IsLocalization.algEquiv (.powers r) (Localization.Away r) S)⟩⟩

/-- A finite product of finite products of principal localizations is again a
finite product of principal localizations. -/
theorem pi {R : Type u} {n : ℕ} (S : Fin n → Type u) [CommRing R]
    [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (h : ∀ i, IsFiniteProductOfPrincipalLocalizations R (S i)) :
    IsFiniteProductOfPrincipalLocalizations R ((i : Fin n) → S i) := by
  classical
  choose m f e using h
  let ι := Σ i : Fin n, Fin (m i)
  let eι := Fintype.equivFin ι
  let curry : ((p : ι) → Localization.Away (f p.1 p.2)) ≃ₐ[R]
      ((i : Fin n) → (j : Fin (m i)) → Localization.Away (f i j)) :=
    { toFun := fun x i j ↦ x ⟨i, j⟩
      invFun := fun x p ↦ x p.1 p.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact ⟨Fintype.card ι, fun k ↦ f (eι.symm k).1 (eι.symm k).2,
    ⟨(AlgEquiv.piCongrLeft R (fun p : ι ↦ Localization.Away (f p.1 p.2)) eι.symm).trans
      (curry.trans (AlgEquiv.piCongrRight fun i ↦ Classical.choice (e i)))⟩⟩

/-- Finite products of principal localizations are preserved by compatible
isomorphisms of the base and target rings. -/
theorem of_ringEquiv {R S R' S' : Type u} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S']
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcomm : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r))
    (h : IsFiniteProductOfPrincipalLocalizations R S) :
    IsFiniteProductOfPrincipalLocalizations R' S' := by
  obtain ⟨n, f, ⟨e⟩⟩ := h
  let l (i : Fin n) : Localization.Away (f i) ≃+* Localization.Away (eR (f i)) :=
    IsLocalization.ringEquivOfRingEquiv (M := .powers (f i)) (T := .powers (eR (f i)))
      _ _ eR (by simp)
  let p := RingEquiv.piCongrRight l
  have hp (r : R) : p (algebraMap R _ r) = algebraMap R' _ (eR r) := by
    funext i
    exact IsLocalization.ringEquivOfRingEquiv_eq (M := .powers (f i))
      (T := .powers (eR (f i))) (by simp) r
  refine ⟨n, fun i ↦ eR (f i), ⟨{ p.symm.trans (e.toRingEquiv.trans eS) with
    commutes' := ?_ }⟩⟩
  intro r
  change eS (e (p.symm (algebraMap R' _ r))) = algebraMap R' S' r
  calc
    eS (e (p.symm (algebraMap R' _ r))) =
        eS (e (algebraMap R _ (eR.symm r))) := by
      congr 2
      apply p.injective
      rw [p.apply_symm_apply, hp, eR.apply_symm_apply]
    _ = eS (algebraMap R S (eR.symm r)) := by rw [e.commutes]
    _ = algebraMap R' S' r := by rw [hcomm, eR.apply_symm_apply]

/-- Finite products of principal localizations are local isomorphisms. -/
theorem isLocalIso {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : IsFiniteProductOfPrincipalLocalizations R S) : Algebra.IsLocalIso R S := by
  obtain ⟨n, f, ⟨e⟩⟩ := h
  letI : IsLocalIso R ((i : Fin n) → Localization.Away (f i)) :=
    IsLocalIso.pi_of_finite R _
  exact IsLocalIso.of_algEquiv e

end IsFiniteProductOfPrincipalLocalizations

end Algebra

namespace CommRingCat

/-- The morphism property on `CommRingCat` consisting of finite products of
principal localizations. -/
abbrev finiteProductOfPrincipalLocalizations : MorphismProperty CommRingCat.{u} :=
  fun _ _ f ↦ @Algebra.IsFiniteProductOfPrincipalLocalizations _ _ _ _ f.hom.toAlgebra

/-- A morphism of commutative rings is a finite product of principal
localizations precisely when the induced algebra structure satisfies
`Algebra.IsFiniteProductOfPrincipalLocalizations`. -/
theorem finiteProductOfPrincipalLocalizations_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    finiteProductOfPrincipalLocalizations f ↔
      @Algebra.IsFiniteProductOfPrincipalLocalizations R S _ _ f.hom.toAlgebra :=
  Iff.rfl

/-- Finite products of principal localizations are local isomorphisms. -/
theorem finiteProductOfPrincipalLocalizations_le_localIso :
    (finiteProductOfPrincipalLocalizations : MorphismProperty CommRingCat.{u}) ≤ localIso := by
  intro R S f hf
  letI := f.hom.toAlgebra
  exact Algebra.IsFiniteProductOfPrincipalLocalizations.isLocalIso hf

/-- Finite products of principal localizations are invariant under
isomorphisms. -/
instance finiteProductOfPrincipalLocalizations_respectsIso :
    CommRingCat.finiteProductOfPrincipalLocalizations.RespectsIso := by
  refine RespectsIso.of_respects_arrow_iso _ fun f g e hf ↦ ?_
  letI := f.hom.hom.toAlgebra
  letI := g.hom.hom.toAlgebra
  exact Algebra.IsFiniteProductOfPrincipalLocalizations.of_ringEquiv
    (Comma.leftIso e).commRingCatIsoToRingEquiv (Comma.rightIso e).commRingCatIsoToRingEquiv
    (fun r ↦ (ConcreteCategory.congr_hom e.hom.w r).symm) hf

end CommRingCat

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map has an ind-(Zariski localization) presentation in universe `w`
if it is a filtered colimit of finite products of principal localizations in
that universe. -/
abbrev IndZariskiLocalization.Raw (f : R →+* A) : Prop :=
  ind.{w, max u v, max u v + 1} CommRingCat.finiteProductOfPrincipalLocalizations
    (CommRingCat.ofHom f.ulift.{v, u})

/-- A ring map is an ind-(Zariski localization) when it is a filtered colimit
of finite products of principal localizations, with presentation universe equal
to the maximum of the endpoint universes. -/
abbrev IndZariskiLocalization (f : R →+* A) : Prop :=
  IndZariskiLocalization.Raw.{u, v, max u v} f

end

namespace IndZariskiLocalization

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- An arbitrary-size categorical presentation induces the canonical
ind-(Zariski localization) predicate. -/
theorem ofRaw (f : R →+* A) (h : IndZariskiLocalization.Raw.{u, v, w} f) :
    f.IndZariskiLocalization :=
  sorry

/-- An ind-(Zariski localization) is ind-Zariski. -/
theorem indZariski (f : R →+* A) (h : f.IndZariskiLocalization) : f.IndZariski := by
  obtain ⟨J, hJ, hfiltered, D, t, s, hc, hD⟩ := h
  exact ⟨J, hJ, hfiltered, D, t, s, hc, fun j ↦
    ⟨CommRingCat.finiteProductOfPrincipalLocalizations_le_localIso _ (hD j).1, (hD j).2⟩⟩

end

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite product of principal localizations is an ind-(Zariski
localization). -/
theorem of_finiteProduct (h : Algebra.IsFiniteProductOfPrincipalLocalizations R A) :
    (algebraMap R A).IndZariskiLocalization := by
  apply MorphismProperty.le_ind
  letI := (algebraMap R A).ulift.{u, u}.toAlgebra
  exact Algebra.IsFiniteProductOfPrincipalLocalizations.of_ringEquiv
    ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ ↦ rfl) h

/-- A principal localization map is an ind-(Zariski localization). -/
theorem of_localizationAway (r : R) :
    (algebraMap R (Localization.Away r)).IndZariskiLocalization := by
  exact of_finiteProduct
    (Algebra.IsFiniteProductOfPrincipalLocalizations.of_localizationAway r)

end

end IndZariskiLocalization

end RingHom
