/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

/-!
# Source loci of scheme-morphism properties

This module defines the largest candidate open in the source of a scheme
morphism on which a given morphism property holds, together with its locality
and standard-topology transport interfaces.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace CategoryTheory.MorphismProperty

variable (P : MorphismProperty Scheme.{u}) {X Y X' : Scheme.{u}}

/-- The supremum of the source opens on which `f` has property `P`. -/
def sourceLocus (f : X ⟶ Y) : X.Opens :=
  sSup {U : X.Opens | P (U.ι ≫ f)}

/-- A point belongs to `P.sourceLocus f` exactly when it belongs to some source
open on which the restriction of `f` has property `P`. -/
theorem mem_sourceLocus (f : X ⟶ Y) (x : X) :
    x ∈ P.sourceLocus f ↔ ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := by
  simp [sourceLocus, TopologicalSpace.Opens.mem_sSup, and_comm]

/-- Every source open on which the restriction of `f` has property `P` is
contained in `P.sourceLocus f`. -/
theorem sourceLocus_maximal (f : X ⟶ Y) (U : X.Opens)
    (hU : P (U.ι ≫ f)) : U ≤ P.sourceLocus f := by
  exact le_sSup hU

/-- For a Zariski-local source property, `P.sourceLocus f` is the greatest
source open on which the restriction of `f` has property `P`. -/
theorem sourceLocus_isGreatest [IsZariskiLocalAtSource P] (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (P.sourceLocus f) := by
  refine ⟨?_, fun U hU ↦ P.sourceLocus_maximal f U hU⟩
  change P ((sSup {U : X.Opens | P (U.ι ≫ f)}).ι ≫ f)
  rw [sSup_eq_iSup']
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.Opens.iSupOpenCover (fun U : {U : X.Opens // P (U.ι ≫ f)} ↦ U.1))
  intro U
  change P (X.homOfLE (le_iSup _ U) ≫ _ ≫ f)
  exact (X.homOfLE_ι_assoc (le_iSup _ U) f).symm ▸ U.2

/-- For a Zariski-local source property, the source locus is all of the source
exactly when the original morphism has the property. -/
theorem sourceLocus_eq_top_iff [IsZariskiLocalAtSource P] (f : X ⟶ Y) :
    P.sourceLocus f = ⊤ ↔ P f := by
  constructor
  · intro h
    have hf := (P.sourceLocus_isGreatest f).1
    rw [h] at hf
    exact (P.cancel_left_of_respectsIso X.topIso.hom f).mp hf
  · intro hf
    exact top_unique (P.sourceLocus_maximal f ⊤
      ((P.cancel_left_of_respectsIso X.topIso.hom f).mpr hf))

/-- For a source property local in a non-Zariski standard topology,
`P.sourceLocus f` is the greatest source open on which `f` has property `P`. -/
theorem sourceLocus_isGreatest_nonZariski
    (tau : StandardTopology) (h_tau : tau ≠ .zariski)
    [P.IsLocalAtSource tau.precoverage] (f : X ⟶ Y) :
    IsGreatest {U : X.Opens | P (U.ι ≫ f)} (P.sourceLocus f) := by
  have hle : Scheme.zariskiPrecoverage ≤ tau.precoverage := by
    cases tau with
    | zariski => exact (h_tau rfl).elim
    | etale =>
      apply Scheme.precoverage_mono
      intro A B a ha
      letI : IsOpenImmersion a := ha
      exact HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
    | smooth =>
      apply Scheme.precoverage_mono
      intro A B a ha
      letI : IsOpenImmersion a := ha
      infer_instance
    | syntomic =>
      -- This needs the complete-intersection-fiber theory for open immersions.
      sorry
    | fppf => exact Scheme.zariskiPrecoverage_le_fppfPrecoverage
  letI : IsZariskiLocalAtSource P := IsLocalAtSource.of_le hle
  exact P.sourceLocus_isGreatest f

/-- Source locality preserves precomposition with any member of the covering property. -/
private theorem precomp_of_source_local
    (P Q : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage Q)]
    (hQ : @IsOpenImmersion ≤ Q)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (ha : Q a) (hb : P b) :
    P (a ≫ b) := by
  let cover := B.affineCover.changeProp (Q := Q) (fun i ↦ hQ _ inferInstance)
  exact (P.iff_of_zeroHypercover_source (cover.add a ha)).mp hb .none

/-- For an open covering property, the image of each good source open is good by descent. -/
private theorem sourceLocus_preimage_of_precoverage
    (P Q : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource (Scheme.precoverage Q)]
    [IsZariskiLocalAtSource Q] [Q.IsStableUnderBaseChange]
    (hQ : @IsOpenImmersion ≤ Q)
    (hopen : ∀ {A B : Scheme.{u}} (a : A ⟶ B), Q a → IsOpenMap a)
    {X Y X' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ X) (hg : Q g) :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := by
  letI : IsZariskiLocalAtSource P :=
    IsLocalAtSource.of_le (Scheme.precoverage_mono hQ)
  apply le_antisymm
  · apply P.sourceLocus_maximal
    have hrestrict : Q (g ∣_ P.sourceLocus f) :=
      Q.of_isPullback (isPullback_morphismRestrict g (P.sourceLocus f)).flip hg
    have hp := precomp_of_source_local P Q hQ
      (g ∣_ P.sourceLocus f) ((P.sourceLocus f).ι ≫ f) hrestrict
      (P.sourceLocus_isGreatest f).1
    simpa only [← Category.assoc, morphismRestrict_ι] using hp
  · intro x hx
    obtain ⟨V, hxV, hV⟩ := (P.mem_sourceLocus (g ≫ f) x).mp hx
    let a := V.ι ≫ g
    have ha : Q a := IsZariskiLocalAtSource.comp hg V.ι
    let W : X.Opens := ⟨Set.range a, (hopen a ha).isOpen_range⟩
    let i := IsOpenImmersion.lift W.ι a (by simp only [Scheme.Opens.range_ι]; rfl)
    have hi : Q i := Q.of_postcomp (W' := @IsOpenImmersion) i W.ι inferInstance (by
      simpa only [i, IsOpenImmersion.lift_fac] using ha)
    have hsurj : Function.Surjective i.base := by
      intro y
      obtain ⟨z, hz⟩ := y.2
      refine ⟨z, ?_⟩
      apply W.ι.isOpenEmbedding.injective
      change (i ≫ W.ι) z = y.1
      simpa only [i, IsOpenImmersion.lift_fac] using hz
    have hW : P (W.ι ≫ f) := by
      apply IsLocalAtSource.of_forall_comp (K := Scheme.precoverage Q)
        ((Scheme.singleton_mem_precoverage_iff Q i).mpr ⟨hsurj, hi⟩)
      rintro _ _ ⟨⟩
      simpa only [← Category.assoc, i, IsOpenImmersion.lift_fac, a] using hV
    exact P.sourceLocus_maximal f W hW (show g x ∈ W from ⟨⟨x, hxV⟩, rfl⟩)

/-- The source locus of an fppf-local property commutes with preimage along a
flat, locally finitely presented morphism. -/
theorem sourceLocus_preimage_fppf
    [P.IsLocalAtSource Scheme.fppfPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFinitePresentation g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := by
  letI : P.IsLocalAtSource
      (Scheme.precoverage ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation)) :=
    ‹P.IsLocalAtSource Scheme.fppfPrecoverage›
  refine sourceLocus_preimage_of_precoverage P
    ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation)
    (fun {_ _} a ha ↦ ?_) (fun {_ _} a ha ↦ ?_) f g ⟨inferInstance, inferInstance⟩
  · letI : IsOpenImmersion a := ha
    exact ⟨HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities,
      locallyOfFinitePresentation_of_isOpenImmersion a⟩
  · letI : Flat a := ha.1
    letI : LocallyOfFinitePresentation a := ha.2
    exact a.isOpenMap

/-- The source locus of a syntomic-local property commutes with preimage along
a syntomic morphism. -/
theorem sourceLocus_preimage_syntomic
    [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Syntomic g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := sorry

/-- The source locus of a smooth-local property commutes with preimage along a
smooth morphism. -/
theorem sourceLocus_preimage_smooth
    [P.IsLocalAtSource Scheme.bigSmoothPrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Smooth g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := by
  refine sourceLocus_preimage_of_precoverage P (@Smooth : MorphismProperty Scheme.{u})
    (fun {_ _} a ha ↦ ?_) (fun {_ _} a ha ↦ ?_) f g inferInstance
  · letI : IsOpenImmersion a := ha
    infer_instance
  · letI : Smooth a := ha
    letI : Flat a := ⟨fun {_} hU {_} hV e ↦ (a.smooth_appLE hU hV e).flat⟩
    letI : LocallyOfFinitePresentation a :=
      ⟨fun {_} hU {_} hV e ↦ (a.smooth_appLE hU hV e).finitePresentation⟩
    exact a.isOpenMap

/-- The source locus of an étale-local property commutes with preimage along an
étale morphism. -/
theorem sourceLocus_preimage_etale
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    (f : X ⟶ Y) (g : X' ⟶ X) [Etale g] :
    g ⁻¹ᵁ P.sourceLocus f = P.sourceLocus (g ≫ f) := by
  letI : P.IsLocalAtSource (Scheme.precoverage (@Etale : MorphismProperty Scheme.{u})) :=
    ‹P.IsLocalAtSource Scheme.etalePrecoverage›
  refine sourceLocus_preimage_of_precoverage P (@Etale : MorphismProperty Scheme.{u})
    (fun {_ _} a ha ↦ ?_) (fun {_ _} a ha ↦ ?_) f g inferInstance
  · letI : IsOpenImmersion a := ha
    infer_instance
  · letI : Etale a := ha
    letI : Flat a := ⟨fun {_} hU {_} hV e ↦
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp (a.etale_appLE hU hV e)).1⟩
    letI : LocallyOfFinitePresentation a :=
      ⟨fun {_} hU {_} hV e ↦
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp (a.etale_appLE hU hV e)).2.2⟩
    exact a.isOpenMap

end CategoryTheory.MorphismProperty
