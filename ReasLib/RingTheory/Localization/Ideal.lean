/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal

/-!
# Quotients by ideals in localizations

This module gives the normal form for a quotient by an ideal of an arbitrary
localization: contract the ideal to the source ring, then localize the source
quotient.  Mathlib owns the underlying localization instance; this leaf only
packages the transport from the mapped contraction back to the original ideal.
-/

@[expose] public section

universe u v

namespace IsLocalization

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (M : Submonoid R) [IsLocalization M S]

/-- Tag `0AUG`: if `S` is the localization of `R` at `M`, then quotienting `S` by `K` is the
localization of `R ⧸ K.under R` at the image of `M`. This is the contraction-normalized form
of mathlib's quotient-localization instance. -/
@[stacks 0AUG "contraction-normalized quotient localization"]
noncomputable def quotientAlgEquivOfUnder (K : Ideal S) :
    Localization (Algebra.algebraMapSubmonoid (R ⧸ K.under R) M) ≃ₐ[R ⧸ K.under R]
      S ⧸ K := by
  let J : Ideal R := K.under R
  let Kmap : Ideal S := Ideal.map (algebraMap R S) J
  -- Local instance justification (defeq pin): select mathlib's canonical quotient algebra.
  letI : Algebra (R ⧸ J) (S ⧸ Kmap) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  have hKmap : Kmap = K := IsLocalization.map_under M S K
  -- Local instance justification (proof-local temporary data): transport the lying-over proof.
  letI : Kmap.LiesOver J := ⟨by
    simpa [Ideal.under_def, J, hKmap]⟩
  -- Local instance justification (defeq pin): `K` lies over its canonical contraction.
  letI : K.LiesOver J := ⟨by
    simpa [Ideal.under_def, J]⟩
  let eLoc :
      Localization (Algebra.algebraMapSubmonoid (R ⧸ J) M) ≃ₐ[R ⧸ J] (S ⧸ Kmap) :=
    Localization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ J) M) (S ⧸ Kmap)
  let eQuot : (S ⧸ Kmap) ≃ₐ[R ⧸ J] (S ⧸ K) := by
    have hmap_refl (L : Ideal S) :
        Ideal.map (AlgEquiv.refl : S ≃ₐ[R] S) L = L := by
      change Ideal.map (RingHom.id S) L = L
      simpa using (Ideal.map_id (I := L))
    have hKmap' : K = Ideal.map (AlgEquiv.refl : S ≃ₐ[R] S) Kmap := by
      calc
        K = Ideal.map (AlgEquiv.refl : S ≃ₐ[R] S) K := (hmap_refl K).symm
        _ = Ideal.map (AlgEquiv.refl : S ≃ₐ[R] S) Kmap := by
          simpa using
            congrArg (fun L : Ideal S ↦ Ideal.map (AlgEquiv.refl : S ≃ₐ[R] S) L) hKmap.symm
    exact Ideal.Quotient.algEquivOfEqMap
      (p := J) (P := Kmap) (Q := K) (σ := (AlgEquiv.refl : S ≃ₐ[R] S)) hKmap'
  exact eLoc.trans eQuot

/-- Tag `0AUG`: on a source-ring generator, `quotientAlgEquivOfUnder` sends the localized
quotient class to the corresponding class in `S ⧸ K`. -/
@[simp, stacks 0AUG "contraction-normalized quotient-localization generator"]
theorem quotientAlgEquivOfUnder_apply_mk (K : Ideal S) (x : R) :
    quotientAlgEquivOfUnder M K
        (algebraMap (R ⧸ K.under R)
          (Localization (Algebra.algebraMapSubmonoid (R ⧸ K.under R) M))
          (Ideal.Quotient.mk (K.under R) x)) =
      Ideal.Quotient.mk K (algebraMap R S x) := sorry

end IsLocalization

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- The canonical `R`-linear comparison between the localization of an ideal and its ideal map
to the localized ring.  This is the arbitrary-submonoid owner; prime-local and principal-open
views are thin specializations of it. -/
@[stacks 0523 "localized ideal comparison"]
noncomputable def localizationMapEquiv (T : Submonoid R) (I : Ideal R) :
    LocalizedModule T I ≃ₗ[R]
      Ideal.map (algebraMap R (Localization T)) I :=
  IsLocalizedModule.linearEquiv T
    (LocalizedModule.mkLinearMap T I)
    (Algebra.idealMap I (S := Localization T))

/-- The canonical ideal-localization comparison sends a localized source generator to its mapped
ideal generator. -/
@[simp, stacks 0523 "localized ideal comparison on generators"]
theorem localizationMapEquiv_apply_mk (T : Submonoid R) (I : Ideal R) (x : I) :
    localizationMapEquiv T I (LocalizedModule.mkLinearMap T I x) =
      Algebra.idealMap I (S := Localization T) x := sorry

end Ideal

namespace Localization.BaseIdeal

section

universe w

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable (M : Submonoid A) (I : Ideal R)
variable (Aₘ : Type w) [CommRing Aₘ] [Algebra A Aₘ] [Algebra R Aₘ]
variable [IsScalarTower R A Aₘ] [IsLocalization M Aₘ]

/-- Tag `087P`: the canonical comparison from the localization of an algebra quotient to the
quotient of the localized algebra.  The owner keeps the base ideal `I : Ideal R` explicit, rather
than replacing it by a saturation or a contracted ideal. -/
@[stacks 087P "base-ideal quotient-localization ring equivalence"]
noncomputable def ringEquiv :
    Localization
        (Algebra.algebraMapSubmonoid
          (A ⧸ Ideal.map (algebraMap R A) I) M) ≃+*
      Aₘ ⧸ Ideal.map (algebraMap R Aₘ) I :=
  (Localization.algEquiv
      (Algebra.algebraMapSubmonoid
        (A ⧸ Ideal.map (algebraMap R A) I) M)
      (Aₘ ⧸ Ideal.map (algebraMap A Aₘ) (Ideal.map (algebraMap R A) I))).toRingEquiv.trans
    (Ideal.quotEquivOfEq (by
      rw [Ideal.map_map]
      congr 1
      simpa only [IsScalarTower.algebraMap_eq R A Aₘ]))

/-- Tag `087P`: the base-ideal quotient-localization comparison sends a quotient algebra
generator to the corresponding localized quotient class. -/
@[simp, stacks 087P "base-ideal quotient-localization on generators"]
theorem ringEquiv_apply_algebraMap (a : A) :
    ringEquiv M I Aₘ
        (algebraMap (A ⧸ Ideal.map (algebraMap R A) I)
          (Localization
            (Algebra.algebraMapSubmonoid
              (A ⧸ Ideal.map (algebraMap R A) I) M))
          (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) a)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R Aₘ) I)
        (algebraMap A Aₘ a) := sorry

/-- Tag `087P`: the inverse base-ideal quotient-localization comparison sends a localized
quotient generator back to its quotient-localization class. -/
@[simp, stacks 087P "inverse base-ideal quotient-localization on generators"]
theorem ringEquiv_symm_apply_algebraMap (a : A) :
    (ringEquiv M I Aₘ).symm
        (Ideal.Quotient.mk (Ideal.map (algebraMap R Aₘ) I)
          (algebraMap A Aₘ a)) =
      algebraMap (A ⧸ Ideal.map (algebraMap R A) I)
        (Localization
          (Algebra.algebraMapSubmonoid
            (A ⧸ Ideal.map (algebraMap R A) I) M))
        (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) a) := sorry

noncomputable local instance baseIdealQuotientAlgebra :
    Algebra (A ⧸ Ideal.map (algebraMap R A) I)
      (Aₘ ⧸ Ideal.map (algebraMap R Aₘ) I) :=
  (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom R A Aₘ) I).toRingHom.toAlgebra

/-- The base-ideal quotient-localization comparison as an algebra equivalence over the original
quotient algebra. -/
@[stacks 087P "base-ideal quotient-localization algebra equivalence"]
noncomputable def algEquiv :
    Localization
        (Algebra.algebraMapSubmonoid
          (A ⧸ Ideal.map (algebraMap R A) I) M) ≃ₐ[A ⧸ Ideal.map (algebraMap R A) I]
      Aₘ ⧸ Ideal.map (algebraMap R Aₘ) I := by
  refine AlgEquiv.ofRingEquiv (f := ringEquiv M I Aₘ) ?_
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ringEquiv_apply_algebraMap]
  exact
    (AlgHom.BaseIdeal.quotientMap_apply_mk
      (IsScalarTower.toAlgHom R A Aₘ) I a).symm

end

section Self

variable {R : Type u} [CommRing R]
variable (M : Submonoid R) (I : Ideal R)
variable (Rₘ : Type v) [CommRing Rₘ] [Algebra R Rₘ]
variable [IsLocalization M Rₘ]

/-- The base-ideal quotient-localization comparison for a localization of the base ring itself.
This specialization normalizes `map (algebraMap R R) I` to `I`, so consumers can work with the
canonical quotient `R ⧸ I` directly. -/
@[stacks 087P "base-ring quotient-localization algebra equivalence"]
noncomputable def selfAlgEquiv :
    Localization (Algebra.algebraMapSubmonoid (R ⧸ I) M) ≃ₐ[R ⧸ I]
      Rₘ ⧸ Ideal.map (algebraMap R Rₘ) I := by
  exact Localization.algEquiv
    (Algebra.algebraMapSubmonoid (R ⧸ I) M)
    (Rₘ ⧸ Ideal.map (algebraMap R Rₘ) I)

end Self

end Localization.BaseIdeal
