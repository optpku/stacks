/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Finite
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Affine.Cover.Basic

/-!
# Standard covers on the big affine Zariski site

This leaf turns finite standard Zariski covers of affine schemes over a fixed
base into a pretopology on the big affine Zariski carrier.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- A standard Zariski cover of the source of an object of the big affine
Zariski site. The underlying cover data is `Scheme.StandardZariskiCover`. -/
@[stacks 020T "big affine standard cover"]
abbrev BigAffineZariskiStandardCover (U : S.bigAffineZariskiSite) :=
  U.obj.left.StandardZariskiCover.{u, u}

namespace BigAffineZariskiStandardCover

/-- The `i`-th distinguished-open member of a big affine Zariski standard
cover, viewed as an affine scheme over the original base. -/
abbrev siteObj {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) (i : 𝒰.index) : S.bigAffineZariskiSite :=
  StandardZariskiCover.affineOverObj U 𝒰 i

/-- The `i`-th distinguished-open immersion in a big affine Zariski standard
cover. -/
abbrev siteMap {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) (i : 𝒰.index) :
    siteObj S 𝒰 i ⟶ U :=
  StandardZariskiCover.affineOverMap U 𝒰 i

/-- The presieve represented by a big affine Zariski standard cover. -/
abbrev presieve {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) : Presieve U :=
  StandardZariskiCover.affineOverPresieve U 𝒰

/-- The distinguished opens of a big affine standard cover have supremum
`⊤` in the source scheme. -/
theorem iSup_eq_top {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) :
    (⨆ i : 𝒰.index, 𝒰.opens i) = (⊤ : U.obj.left.Opens) :=
  StandardZariskiCover.iSup_eq_top 𝒰

end BigAffineZariskiStandardCover

/-- A standard covering is a finite Zariski covering whose component maps have
principal-open image. The component schemes may be arbitrary isomorphic copies
of the principal opens, as in the Stacks definition. -/
@[stacks 020T]
def bigAffineZariskiCovering {U : S.bigAffineZariskiSite} (R : Presieve U) : Prop :=
  R.uncurry.Finite ∧
    R.map (AffineOver.toScheme S) ∈ Scheme.precoverage @IsOpenImmersion U.obj.left ∧
    ∀ ⦃V⦄ (f : V ⟶ U), R f →
      ∃ r : Γ(U.obj.left, ⊤),
        Set.range ((AffineOver.toScheme S).map f) = (U.obj.left.basicOpen r : Set U.obj.left)

/-- A standard big affine Zariski cover presents a covering presieve. -/
theorem bigAffineZariskiCovering_ofStandardCover {U : S.bigAffineZariskiSite}
    (𝒰 : BigAffineZariskiStandardCover S U) :
    bigAffineZariskiCovering S (BigAffineZariskiStandardCover.presieve S 𝒰) := by
  letI : Finite 𝒰.index := 𝒰.finiteIndex
  refine ⟨Precoverage.ofArrows_mem_finite _ _, ?_, ?_⟩
  · change (Presieve.ofArrows (StandardZariskiCover.affineOverObj U 𝒰)
        (StandardZariskiCover.affineOverMap U 𝒰)).map (AffineOver.toScheme S) ∈ _
    rw [Presieve.map_ofArrows]
    change Presieve.ofArrows 𝒰.X 𝒰.f ∈ Scheme.precoverage @IsOpenImmersion U.obj.left
    exact 𝒰.toOpenCover.mem₀
  · rintro V f ⟨i⟩
    exact ⟨𝒰.generator i, Scheme.Opens.range_ι _⟩

/-- The standard-covering predicate records finiteness, the Zariski covering
condition, and principal-open images. -/
theorem bigAffineZariskiCovering_iff {U : S.bigAffineZariskiSite} {R : Presieve U} :
    bigAffineZariskiCovering S R ↔
      R.uncurry.Finite ∧
        R.map (AffineOver.toScheme S) ∈ Scheme.precoverage @IsOpenImmersion U.obj.left ∧
        ∀ ⦃V⦄ (f : V ⟶ U), R f →
          ∃ r : Γ(U.obj.left, ⊤),
            Set.range ((AffineOver.toScheme S).map f) =
              (U.obj.left.basicOpen r : Set U.obj.left) :=
  Iff.rfl

private theorem mem_generate_of_range_subset {U V W : S.bigAffineZariskiSite}
    {R : Presieve U} (f : V ⟶ U) (g : W ⟶ U)
    [IsOpenImmersion ((AffineOver.toScheme S).map g)] (hg : R g)
    (h : Set.range ((AffineOver.toScheme S).map f) ⊆
      Set.range ((AffineOver.toScheme S).map g)) : Sieve.generate R f := by
  let F := AffineOver.toScheme S
  let l := IsOpenImmersion.lift (F.map g) (F.map f) h
  have hl : l ≫ F.map g = F.map f := IsOpenImmersion.lift_fac _ _ h
  let k : V ⟶ W := AffineOver.homMk l (by
    calc
      l ≫ W.obj.hom = l ≫ (F.map g ≫ U.obj.hom) :=
        congrArg (fun b ↦ l ≫ b) (AffineOver.hom g).w.symm
      _ = (l ≫ F.map g) ≫ U.obj.hom := (Category.assoc _ _ _).symm
      _ = F.map f ≫ U.obj.hom := congrArg (fun b ↦ b ≫ U.obj.hom) hl
      _ = V.obj.hom := (AffineOver.hom f).w)
  refine ⟨W, k, g, hg, ?_⟩
  apply F.map_injective
  change l ≫ F.map g = F.map f
  exact hl

/-- Every geometric standard covering generates the same sieve as a cover
from the canonical `StandardZariskiCover` owner. The equality makes the result
independent of the finite enumeration and the chosen principal generators. -/
theorem bigAffineZariskiCovering_exists_standardCover
    {U : S.bigAffineZariskiSite} {R : Presieve U} (hR : bigAffineZariskiCovering S R) :
    ∃ 𝒰 : BigAffineZariskiStandardCover S U,
      Sieve.generate R = Sieve.generate (BigAffineZariskiStandardCover.presieve S 𝒰) := by
  classical
  let F := AffineOver.toScheme S
  letI : Fintype R.uncurry := hR.1.fintype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin R.uncurry
  let ι := ULift.{u} (Fin n)
  let a (i : ι) : R.uncurry := e.symm i.down
  have ha : Function.Surjective a := fun x ↦ ⟨⟨e x⟩, e.symm_apply_apply x⟩
  let Y (i : ι) : S.bigAffineZariskiSite := (a i).val.1
  let f (i : ι) : Y i ⟶ U := (a i).val.2
  have hf (i : ι) : R (f i) := (a i).property
  have hpres0 :
      Presieve.ofArrows (fun i : R.uncurry ↦ i.val.1) (fun i ↦ i.val.2) = R := by
    apply le_antisymm
    · rintro V g ⟨i⟩
      exact i.property
    · intro V g hg
      exact Presieve.ofArrows.mk (⟨⟨V, g⟩, hg⟩ : R.uncurry)
  have hpres : Presieve.ofArrows Y f = R := by
    calc
      Presieve.ofArrows Y f =
          Presieve.ofArrows (fun i : R.uncurry ↦ i.val.1) (fun i ↦ i.val.2) :=
        Presieve.ofArrows_comp_eq_of_surjective (fun i : R.uncurry ↦ i.val.2) ha
      _ = R := hpres0
  choose r hr using fun i : ι ↦ hR.2.2 (f i) (hf i)
  have htop : (⨆ i : ι, U.obj.left.basicOpen (r i)) = ⊤ := by
    apply top_unique
    intro x hx
    have hc0 : (Presieve.ofArrows Y f).map F ∈
        Scheme.precoverage @IsOpenImmersion (F.obj U) := by
      rw [hpres]
      exact hR.2.1
    rw [Presieve.map_ofArrows] at hc0
    obtain ⟨i, hi⟩ := (Scheme.ofArrows_mem_precoverage_iff _).mp hc0 |>.1 x
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨i, (hr i).le hi⟩
  haveI : IsAffine U.obj.left := by
    change IsAffine U.left.obj
    infer_instance
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    apply (isAffineOpen_top U.obj.left).iSup_basicOpen_eq_self_iff.mp
    simpa only [iSup_subtype, iSup_range] using htop
  let 𝒰 : BigAffineZariskiStandardCover S U :=
    { index := ι
      finiteIndex := inferInstance
      generator := r
      cover := by
        rw [PrimeSpectrum.basicOpen_one]
        exact (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan).symm }
  refine ⟨𝒰, le_antisymm ?_ ?_⟩
  · rw [Sieve.generate_le_iff]
    intro V g hg
    have hm : Presieve.ofArrows Y f g := hpres.symm ▸ hg
    obtain ⟨i⟩ := hm
    haveI : IsOpenImmersion (F.map (BigAffineZariskiStandardCover.siteMap S 𝒰 i)) :=
      inferInstanceAs (IsOpenImmersion (𝒰.f i))
    apply mem_generate_of_range_subset S (f i)
      (BigAffineZariskiStandardCover.siteMap S 𝒰 i) (Presieve.ofArrows.mk i)
    change Set.range (F.map (f i)) ⊆ Set.range (𝒰.f i)
    exact ((hr i).trans (Scheme.Opens.range_ι (U.obj.left.basicOpen (r i))).symm).le
  · rw [Sieve.generate_le_iff]
    rintro V g ⟨i⟩
    haveI : IsOpenImmersion (F.map (f i)) := hR.2.1.2 (Presieve.map.of (hf i))
    apply mem_generate_of_range_subset S (BigAffineZariskiStandardCover.siteMap S 𝒰 i)
      (f i) (hf i)
    change Set.range (𝒰.f i) ⊆ Set.range (F.map (f i))
    exact ((Scheme.Opens.range_ι (U.obj.left.basicOpen (r i))).trans (hr i).symm).le

/-- Singleton isomorphisms are covering presieves for the big affine Zariski
standard-cover presentation. -/
theorem bigAffineZariskiCovering_hasIsos :
    ∀ ⦃U V : S.bigAffineZariskiSite⦄ (f : V ⟶ U) [IsIso f],
      bigAffineZariskiCovering S (Presieve.singleton f) := by
  intro U V f hf
  refine ⟨(Pretopology.finite S.bigAffineZariskiSite).has_isos f, ?_, ?_⟩
  · change Presieve.singleton f ∈
      (Scheme.precoverage @IsOpenImmersion).comap (AffineOver.toScheme S) U
    exact Precoverage.mem_coverings_of_isIso f
  · rintro W g ⟨⟩
    refine ⟨1, ?_⟩
    rw [Scheme.basicOpen_one]
    exact Set.range_eq_univ.mpr (((AffineOver.toScheme S).map f).homeomorph.surjective)

/-- Big affine standard Zariski covering presieves are stable under pullback. -/
theorem bigAffineZariskiCovering_pullbacks :
    ∀ ⦃U V : S.bigAffineZariskiSite⦄ (f : V ⟶ U) (R : Presieve U),
      bigAffineZariskiCovering S R →
        bigAffineZariskiCovering S (Presieve.pullbackArrows f R) := by
  intro U V f R hR
  refine ⟨(Pretopology.finite S.bigAffineZariskiSite).pullbacks f R hR.1, ?_, ?_⟩
  · exact Precoverage.pullbackArrows_mem
      (J := (Scheme.precoverage @IsOpenImmersion).comap (AffineOver.toScheme S)) f hR.2.1
  · rintro W g ⟨Z, h, hh⟩
    obtain ⟨r, hr⟩ := hR.2.2 h hh
    let F := AffineOver.toScheme S
    haveI : IsOpenImmersion (F.map h) := hR.2.1.2 (Presieve.map.of hh)
    refine ⟨(F.map f).appTop r, ?_⟩
    have he : (F.map h).opensRange = U.obj.left.basicOpen r :=
      TopologicalSpace.Opens.ext hr
    have hsurj : Function.Surjective (PreservesPullback.iso F h f).hom :=
      (PreservesPullback.iso F h f).hom.homeomorph.surjective
    rw [← PreservesPullback.iso_hom_snd F h f]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj,
      Set.image_univ, IsOpenImmersion.range_pullbackSnd, he]
    exact congrArg (fun O : V.obj.left.Opens ↦ (O : Set V.obj.left))
      (Scheme.preimage_basicOpen_top (F.map f) r)

private theorem image_basicOpen_is_basicOpen {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(Y, ⊤))
    (hr : f.opensRange = Y.basicOpen r) (s : Γ(X, ⊤)) :
    ∃ t : Γ(Y, ⊤), f ''ᵁ X.basicOpen s = Y.basicOpen t := by
  have hi : f ''ᵁ (⊤ : X.Opens) = Y.basicOpen r :=
    (Scheme.Hom.image_top_eq_opensRange f).trans hr
  let s' : Γ(Y, Y.basicOpen r) :=
    Y.presheaf.map (eqToHom hi.symm).op ((f.appIso ⊤).inv s)
  have hs : f ''ᵁ X.basicOpen s = Y.basicOpen s' := by
    rw [Scheme.image_basicOpen]
    exact (Scheme.basicOpen_res_eq Y _ _).symm
  obtain ⟨t, ht⟩ := (isAffineOpen_top Y).basicOpen_basicOpen_is_basicOpen r s'
  exact ⟨t, hs.trans ht.symm⟩

/-- Big affine standard Zariski covering presieves are stable under
refinement. -/
theorem bigAffineZariskiCovering_transitive :
    ∀ ⦃U : S.bigAffineZariskiSite⦄ (R : Presieve U)
      (Ti : ∀ ⦃V⦄ (f : V ⟶ U), R f → Presieve V),
      bigAffineZariskiCovering S R →
        (∀ ⦃V⦄ (f : V ⟶ U) (hR : R f), bigAffineZariskiCovering S (Ti f hR)) →
          bigAffineZariskiCovering S (Presieve.bind R Ti) := by
  intro U R Ti hR hTi
  refine ⟨(Pretopology.finite S.bigAffineZariskiSite).transitive R Ti hR.1
    (fun V f hf ↦ (hTi f hf).1), ?_, ?_⟩
  · exact ((Scheme.precoverage @IsOpenImmersion).comap
      (AffineOver.toScheme S)).toPretopology.transitive R Ti hR.2.1
        (fun V f hf ↦ (hTi f hf).2.1)
  · rintro V g ⟨W, b, a, ha, hb, rfl⟩
    let F := AffineOver.toScheme S
    haveI : IsAffine (F.obj U) := by
      change IsAffine U.left.obj
      infer_instance
    haveI : IsOpenImmersion (F.map a) := hR.2.1.2 (Presieve.map.of ha)
    haveI : IsOpenImmersion (F.map b) := (hTi a ha).2.1.2 (Presieve.map.of hb)
    obtain ⟨r, hr⟩ := hR.2.2 a ha
    obtain ⟨s, hs⟩ := (hTi a ha).2.2 b hb
    have he : (F.map a).opensRange = U.obj.left.basicOpen r :=
      TopologicalSpace.Opens.ext hr
    obtain ⟨t, ht⟩ := image_basicOpen_is_basicOpen (F.map a) r he s
    refine ⟨t, ?_⟩
    change Set.range (F.map (b ≫ a)) = _
    rw [F.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hs]
    exact congrArg (fun O : U.obj.left.Opens ↦ (O : Set U.obj.left)) ht

/-- The pretopology on affine schemes over `S` generated by finite standard
Zariski covers. -/
@[stacks 020T]
def bigAffineZariskiPretopology : Pretopology S.bigAffineZariskiSite where
  coverings := fun _ ↦ { R | bigAffineZariskiCovering S R }
  has_isos := bigAffineZariskiCovering_hasIsos S
  pullbacks := bigAffineZariskiCovering_pullbacks S
  transitive := bigAffineZariskiCovering_transitive S

/-- The precoverage underlying the standard big affine Zariski pretopology. -/
abbrev bigAffineZariskiPrecoverage : Precoverage S.bigAffineZariskiSite :=
  (bigAffineZariskiPretopology S).toPrecoverage

/-- Membership in the standard big affine Zariski precoverage is exactly the
finite distinguished-open covering predicate. -/
theorem mem_bigAffineZariskiPrecoverage_iff {U : S.bigAffineZariskiSite} {R : Presieve U} :
    R ∈ bigAffineZariskiPrecoverage S U ↔ bigAffineZariskiCovering S R :=
  Iff.rfl

/-- The big affine Zariski topology generated by standard distinguished-open
coverings. -/
@[stacks 020T]
abbrev bigAffineZariskiTopology : GrothendieckTopology S.bigAffineZariskiSite :=
  (bigAffineZariskiPretopology S).toGrothendieck

/-- The big affine Zariski topology is generated by its standard-cover
pretopology. -/
theorem bigAffineZariskiTopology_def :
    bigAffineZariskiTopology S = (bigAffineZariskiPretopology S).toGrothendieck :=
  rfl

/-- Every standard big affine Zariski covering presieve belongs to the ambient
restricted big-Zariski precoverage. -/
theorem bigAffineZariskiCovering_mem_restrictedPrecoverage
    {U : S.bigAffineZariskiSite} {R : Presieve U} (hR : bigAffineZariskiCovering S R) :
    R ∈ bigAffineZariskiRestrictedPrecoverage S U := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  change Sieve.generate
      ((Presieve.ofArrows Y f).map (AffineOver.forget S)) ∈
    (Scheme.zariskiTopology.over S) U.obj
  rw [Presieve.map_ofArrows]
  change Sieve.generate (Presieve.ofArrows
      (fun i ↦ AffineOver.obj (Y i))
      (fun i ↦ AffineOver.hom (f i))) ∈ (Scheme.zariskiTopology.over S) U.obj
  rw [← Sieve.ofArrows, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  have h := hR.2.1
  rw [Presieve.map_ofArrows] at h
  exact h

end AlgebraicGeometry.Scheme
