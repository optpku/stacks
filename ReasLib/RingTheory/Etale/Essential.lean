/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.RingHom

/-!
# Essentially etale algebras and ring homomorphisms

This module owns the canonical essentially-etale predicates.  As for
`Algebra.EssSmooth`, the primary algebra predicate is intrinsic: formal
etaleness together with essential finite presentation.  The localization of
an etale algebra is exposed as an equivalent presentation, not as the root
representation.
@stack 0GS6
-/

@[expose] public section

universe u v w

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra is essentially etale when it is formally etale and
essentially of finite presentation over `R`. -/
@[stacks 0GS6 "essentially etale algebra predicate"]
class EssEtale : Prop where
  /-- An essentially etale algebra is formally etale. -/
  formallyEtale : FormallyEtale R S
  /-- An essentially etale algebra is essentially of finite presentation. -/
  essFinitePresentation : EssFinitePresentation R S

/-- Characterize essential etaleness by its two intrinsic properties. -/
theorem essEtale_iff_formallyEtale_and_essFinitePresentation :
    EssEtale R S ↔ FormallyEtale R S ∧ EssFinitePresentation R S :=
  ⟨fun h ↦ ⟨h.formallyEtale, h.essFinitePresentation⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Characterize an essentially etale algebra as a localization of an etale
algebra.  This is the presentation used by local structure theorems. -/
theorem essEtale_iff_exists_etale :
    EssEtale R S ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (_ : Algebra R P) (_ : Algebra P S)
        (_ : IsScalarTower R P S) (M : Submonoid P), Etale R P ∧ IsLocalization M S := sorry

/-- A localization of an etale `R`-algebra is essentially etale over `R`. -/
theorem EssEtale.of_isLocalization
    (P : Type w) [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [Etale R P] (M : Submonoid P) [IsLocalization M S] :
    EssEtale R S := by
  haveI : FormallyEtale P S := FormallyEtale.of_isLocalization M
  refine ⟨FormallyEtale.comp R P S, ?_⟩
  obtain ⟨n, I, e, hI⟩ := (FinitePresentation.iff (R := R) (A := P)).mp inferInstance
  letI : Algebra (MvPolynomial (Fin n) R ⧸ I) S :=
    ((algebraMap P S).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R ⧸ I) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine ⟨n, I, hI, inferInstance, inferInstance, M.comap e.toMonoidHom, ?_⟩
  exact IsLocalization.of_ringEquiv_left e.toRingEquiv
    (Submonoid.map_comap_eq_of_surjective e.surjective M) (fun _ ↦ rfl)

/-- An etale algebra is essentially etale. -/
instance EssEtale.of_etale [Etale R S] : EssEtale R S := by
  haveI : IsLocalization (⊥ : Submonoid S) S := IsLocalization.self bot_le
  exact EssEtale.of_isLocalization R S S ⊥

/-- An essentially etale algebra is flat over its base. -/
theorem EssEtale.flat [EssEtale R S] : Module.Flat R S := by
  obtain ⟨P, _, _, _, _, M, hP, hM⟩ := (essEtale_iff_exists_etale R S).mp inferInstance
  letI := hP
  letI := hM
  haveI : Module.Flat P S := IsLocalization.flat S M
  exact Module.Flat.trans R P S

attribute [instance]
  EssEtale.formallyEtale EssEtale.essFinitePresentation EssEtale.flat

end Algebra

namespace RingHom

/-- The map-first essentially-etale predicate, formed with the algebra
structure induced by the ring homomorphism. -/
@[algebraize RingHom.EssEtale.toAlgebra,
  stacks 0GS6 "essentially etale ring-map predicate"]
def EssEtale {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  @Algebra.EssEtale R S _ _ f.toAlgebra

/-- The map-first predicate agrees with the algebra predicate on an ambient
algebra map. -/
theorem essEtale_algebraMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).EssEtale ↔ Algebra.EssEtale R S := by
  rw [EssEtale, toAlgebra_algebraMap]

/-- A ring homomorphism is essentially etale exactly when it is formally
etale and essentially of finite presentation. -/
theorem essEtale_def
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssEtale ↔ f.FormallyEtale ∧ f.EssFinitePresentation := by
  letI := f.toAlgebra
  exact Algebra.essEtale_iff_formallyEtale_and_essFinitePresentation R S

/-- A ring homomorphism is essentially etale exactly when it factors as an
etale map followed by a localization map. -/
theorem essEtale_iff_exists_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    f.EssEtale ↔
      ∃ (P : Type (max u v)) (_ : CommRing P) (g : R →+* P),
        g.Etale ∧ ∃ (M : Submonoid P) (h : P →+* S),
          M.IsLocalizationMap h ∧ f = h.comp g := by
  constructor
  · intro hf
    letI := f.toAlgebra
    obtain ⟨P, _, _, _, _, M, hP, hM⟩ :=
      (Algebra.essEtale_iff_exists_etale R S).mp hf
    exact ⟨P, inferInstance, algebraMap R P, etale_algebraMap.mpr hP,
      M, algebraMap P S, (isLocalization_iff_isLocalizationMap M S).mp hM,
      IsScalarTower.algebraMap_eq R P S⟩
  · rintro ⟨P, _, g, hg, M, h, hM, rfl⟩
    letI := g.toAlgebra
    letI := h.toAlgebra
    letI := (h.comp g).toAlgebra
    haveI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.Etale R P := hg
    haveI : IsLocalization M S := (isLocalization_iff_isLocalizationMap M S).mpr hM
    exact Algebra.EssEtale.of_isLocalization R S P M

namespace EssEtale

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The algebra induced by an essentially etale map is essentially etale. -/
theorem toAlgebra {f : R →+* S} (hf : f.EssEtale) :
    @Algebra.EssEtale R S _ _ f.toAlgebra := hf

/-- An etale ring homomorphism is essentially etale. -/
theorem of_etale {f : R →+* S} (hf : f.Etale) : f.EssEtale := by
  letI := f.toAlgebra
  letI := hf.toAlgebra
  exact Algebra.EssEtale.of_etale R S

/-- A localization ring homomorphism is essentially etale. -/
theorem of_isLocalization (f : R →+* S) (M : Submonoid R)
    (hf : M.IsLocalizationMap f) : f.EssEtale := by
  letI := f.toAlgebra
  haveI : IsLocalization M S := (isLocalization_iff_isLocalizationMap M S).mpr hf
  exact Algebra.EssEtale.of_isLocalization R S R M

/-- An essentially etale ring homomorphism is formally etale. -/
theorem formallyEtale {f : R →+* S} (hf : f.EssEtale) : f.FormallyEtale :=
  (essEtale_def f).mp hf |>.1

/-- An essentially etale ring homomorphism is essentially of finite
presentation. -/
theorem essFinitePresentation {f : R →+* S} (hf : f.EssEtale) :
    f.EssFinitePresentation :=
  (essEtale_def f).mp hf |>.2

/-- An essentially etale ring homomorphism is flat. -/
theorem flat {f : R →+* S} (hf : f.EssEtale) : f.Flat := by
  letI := f.toAlgebra
  letI := hf.toAlgebra
  exact Algebra.EssEtale.flat R S

/-- Composition of essentially etale ring homomorphisms is essentially
etale. -/
theorem comp {f : R →+* S} {g : S →+* T} (hf : f.EssEtale) (hg : g.EssEtale) :
    (g.comp f).EssEtale :=
  (essEtale_def _).mpr
    ⟨hf.formallyEtale.comp hg.formallyEtale, hf.essFinitePresentation.comp hg.essFinitePresentation⟩

/-- Localization-away maps are essentially etale. -/
theorem holdsForLocalizationAway :
    RingHom.HoldsForLocalizationAway RingHom.EssEtale := by
  intro R S _ _ _ r _
  exact of_isLocalization (algebraMap R S) (Submonoid.powers r)
    ((isLocalization_iff_isLocalizationMap _ _).mp inferInstance)

/-- The identity ring homomorphism is essentially etale. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).EssEtale :=
  of_etale (Etale.of_bijective Function.bijective_id)

/-- Essential etaleness is stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition RingHom.EssEtale :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg

/-- Essential etaleness is stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.EssEtale := by
  refine .mk (stableUnderComposition.respectsIso ?_) ?_
  · intro R S _ _ e
    exact of_etale (Etale.of_bijective e.bijective)
  · introv hf
    rw [essEtale_algebraMap] at hf ⊢
    letI := hf
    exact ⟨inferInstance, inferInstance⟩

/-- Essential etaleness is invariant under isomorphisms of ring maps. -/
theorem respectsIso : RingHom.RespectsIso RingHom.EssEtale := by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact of_etale (Etale.of_bijective e.bijective)

end EssEtale

end RingHom
