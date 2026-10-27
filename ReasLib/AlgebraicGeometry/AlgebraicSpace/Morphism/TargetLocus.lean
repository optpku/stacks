/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Openness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.Stability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic.UniversallyOpen

/-!
# Target loci of morphism properties of algebraic spaces

The union of good target opens defines a candidate locus for any morphism property.
For a property local on the target in the fppf, syntomic, smooth, or étale topology,
this locus is good and commutes with base changes admitted by that topology.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The predicate that a precoverage is one of the fppf, syntomic, smooth, or
étale precoverages on algebraic spaces over `S`. -/
def isFppfToEtalePrecoverage {S : Scheme.{u}} (K : Precoverage (AlgebraicSpace S)) :
    Prop :=
  K = fppfPrecoverage S ∨ K = syntomicPrecoverage S ∨
    K = smoothPrecoverage S ∨ K = etalePrecoverage

private theorem targetLocus_openCover_mem {S : Scheme.{u}}
    {K : Precoverage (AlgebraicSpace S)} (hτ : isFppfToEtalePrecoverage K)
    {Y : AlgebraicSpace S} {I : Type v} {U : I → AlgebraicSpace S}
    (ι : ∀ i, U i ⟶ Y) (hι : ∀ i, IsOpenImmersion (ι i))
    (hcover : (⋃ i, Set.range (Points.map (ι i))) = Set.univ) :
    Presieve.ofArrows U ι ∈ K.coverings Y := by
  have hEtale (i) : Etale (ι i) := by
    letI := hι i
    infer_instance
  letI instEtale (i : I) : Etale (ι i) := hEtale i
  rcases hτ with rfl | rfl | rfl | rfl
  · apply (ofArrows_mem_fppfPrecoverage_iff ι).mpr
    exact ⟨fun i ↦ inferInstance, fun i ↦ inferInstance,
      Set.iUnion_eq_univ_iff.mp hcover⟩
  · exact (ofArrows_mem_syntomicPrecoverage_iff ι).mpr
      ⟨fun i ↦ inferInstance, hcover⟩
  · exact (ofArrows_mem_smoothPrecoverage_iff ι).mpr
      ⟨fun i ↦ inferInstance, hcover⟩
  · exact (ofArrows_mem_etalePrecoverage_iff ι).mpr ⟨hEtale, hcover⟩

private theorem targetLocus_precoverage_spec {S : Scheme.{u}}
    {K : Precoverage (AlgebraicSpace S)} (hτ : isFppfToEtalePrecoverage K) :
    ∃ Q : MorphismProperty (AlgebraicSpace S), K = precoverage Q ∧
      Q.IsStableUnderBaseChange ∧ Q.IsStableUnderComposition ∧
      (∀ {A B : AlgebraicSpace S} (i : A ⟶ B), IsOpenImmersion i → Q i) ∧
      Q ≤ pointsIsOpenMap := by
  rcases hτ with rfl | rfl | rfl | rfl
  · have hK : fppfPrecoverage S =
        precoverage ((@Flat S) ⊓ (@LocallyOfFinitePresentation S)) := by
      ext Y R
      obtain ⟨I, U, j, rfl⟩ := R.exists_eq_ofArrows
      rw [ofArrows_mem_fppfPrecoverage_iff, ofArrows_mem_precoverage_iff]
      change ((∀ i, Flat (j i)) ∧ (∀ i, LocallyOfFinitePresentation (j i)) ∧ _) ↔
        (∀ i, Flat (j i) ∧ LocallyOfFinitePresentation (j i)) ∧ _
      simp only [Set.iUnion_eq_univ_iff, forall_and, and_assoc]
    refine ⟨(@Flat S) ⊓ (@LocallyOfFinitePresentation S), hK,
      inferInstance, inferInstance, ?_, ?_⟩
    · intro A B i hi
      letI := hi
      exact ⟨inferInstance, inferInstance⟩
    · intro A B g hg
      letI := hg.1
      letI := hg.2
      exact (inferInstance : Open g).isOpenMap
  · refine ⟨@Syntomic S, rfl, inferInstance, inferInstance, ?_, ?_⟩
    · intro A B i hi
      letI := hi
      infer_instance
    · intro A B g hg
      letI := hg
      exact (inferInstance : Open g).isOpenMap
  · refine ⟨@Smooth S, rfl, inferInstance, inferInstance, ?_, ?_⟩
    · intro A B i hi
      letI := hi
      infer_instance
    · intro A B g hg
      letI := hg
      exact (inferInstance : Open g).isOpenMap
  · refine ⟨@Etale S, rfl, inferInstance, inferInstance, ?_, ?_⟩
    · intro A B i hi
      letI := hi
      infer_instance
    · intro A B g hg
      letI := hg
      exact Etale.isOpenMap g

private theorem targetLocus_precoverage_morphismProperty {S : Scheme.{u}}
    (Q : MorphismProperty (AlgebraicSpace S))
    (hOpen : ∀ {A B : AlgebraicSpace S} (i : A ⟶ B), IsOpenImmersion i → Q i) :
    (precoverage Q).morphismProperty = Q := by
  ext A B g
  constructor
  · rintro ⟨R, hR, hg⟩
    exact hR.2 hg
  · intro hg
    let U : Bool → AlgebraicSpace S := fun b ↦ match b with
      | false => B
      | true => A
    let j : ∀ b, U b ⟶ B := fun b ↦ match b with
      | false => 𝟙 B
      | true => g
    refine ⟨Presieve.ofArrows U j, ?_, Presieve.ofArrows.mk true⟩
    apply (ofArrows_mem_precoverage_iff Q j).mpr
    refine ⟨?_, Set.iUnion_eq_univ_iff.mpr ?_⟩
    · intro b
      cases b
      · exact hOpen _ inferInstance
      · exact hg
    · intro y
      exact ⟨false, y, Points.map_id y⟩

private theorem targetLocus_of_isPullback {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {K : Precoverage (AlgebraicSpace S)}
    [P.IsLocalAtTarget K] {X Y X' Y' : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback a f' f g) (hg : K.morphismProperty g) (hf : P f) : P f' := by
  obtain ⟨R, hR, hg⟩ := hg
  rw [← P.cancel_left_of_respectsIso sq.isoPullback.inv, sq.isoPullback_inv_snd]
  exact MorphismProperty.IsLocalAtTarget.pullbackSnd hR hg hf

/-- The underlying points of the target locus of `P` at `f`, namely the union of
point-sets of open subspaces of `Y` along which the restriction of `f` has `P`. -/
def targetLocusPoints {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Set (Points Y) :=
  {y | ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι)}

/-- A point of `Y` lies in `targetLocusPoints P f` if and only if it lies in some
open subspace of `Y` along which the restriction of `f` has `P`. -/
theorem mem_targetLocusPoints {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {y : Points Y} :
    y ∈ targetLocusPoints P f ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι) :=
  Iff.rfl

/-- `targetLocusPoints P f` is open in `|Y|`. -/
theorem isOpen_targetLocusPoints {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen (targetLocusPoints P f) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro y ⟨U, hy, hU⟩
  exact ⟨U.pointsSet, fun z hz ↦ ⟨U, hz, hU⟩, U.isOpen_pointsSet, hy⟩

/-- The candidate target locus obtained from the union of good open subspaces.
Its restriction has `P` when `P` is local on the target for one of the fppf,
syntomic, smooth, or étale precoverages. -/
def targetLocus {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : OpenSubspace Y :=
  OpenSubspace.fromOpens ⟨targetLocusPoints P f, isOpen_targetLocusPoints P f⟩

/-- The underlying point-set of `targetLocus P f` is `targetLocusPoints P f`. -/
theorem targetLocus_pointsSet {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (targetLocus P f).pointsSet = targetLocusPoints P f := by
  exact OpenSubspace.fromOpens_pointsSet _

/-- A point of `Y` lies in `targetLocus P f` if and only if it lies in some open
subspace of `Y` along which the restriction of `f` has `P`. -/
theorem mem_targetLocus {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {y : Points Y} :
    y ∈ (targetLocus P f).pointsSet ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι) := by
  rw [targetLocus_pointsSet]
  exact mem_targetLocusPoints P f

/-- Every open subspace of `Y` along which the restriction of `f` has `P` factors
through `targetLocus P f`. -/
theorem targetLocus_maximal {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : OpenSubspace Y) (hV : P (pullback.snd f V.ι)) :
    ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι := by
  apply (V.pointsSet_subset_iff (targetLocus P f)).mp
  intro y hy
  exact (mem_targetLocus P f).mpr ⟨V, hy, hV⟩

/-- `targetLocus P f` occupies `targetLocusPoints P f`, and is unique up to unique
lift over `Y`. -/
theorem targetLocus_spec {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (targetLocus P f).pointsSet = targetLocusPoints P f ∧
      ∀ V : OpenSubspace Y, V.pointsSet = targetLocusPoints P f →
        ∃! χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι := by
  refine ⟨targetLocus_pointsSet P f, ?_⟩
  intro V hV
  have hsubset : V.pointsSet ⊆ (targetLocus P f).pointsSet := by
    rw [hV, targetLocus_pointsSet]
  obtain ⟨χ, hχ⟩ := (V.pointsSet_subset_iff (targetLocus P f)).mp hsubset
  letI : Mono (targetLocus P f).ι := (targetLocus P f).spec.2
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  exact (cancel_mono (targetLocus P f).ι).mp (hψ.trans hχ.symm)

/-- For a property local on the target in the fppf, syntomic, smooth, or étale
topology, the target locus has the property and every good open subspace factors
through its inclusion. -/
theorem targetLocus_isLargest {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P (pullback.snd f (targetLocus P f).ι) ∧
      ∀ V : OpenSubspace Y, P (pullback.snd f V.ι) →
        ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι := by
  refine ⟨?_, fun V hV ↦ targetLocus_maximal P f V hV⟩
  let W := targetLocus P f
  let I := {V : OpenSubspace Y // P (pullback.snd f V.ι)}
  let j (V : I) : V.val.X ⟶ W.X :=
    OpenSubspace.Construction.lift V.val.ι
      (fun y hy ↦ ⟨V.val, hy, V.property⟩)
  have hj (V : I) : j V ≫ W.ι = V.val.ι :=
    OpenSubspace.Construction.lift_ι _ _
  letI : IsOpenImmersion W.ι := W.isOpenImmersion
  have hjOpen (V : I) : IsOpenImmersion (j V) := by
    letI := V.val.isOpenImmersion
    exact IsOpenImmersion.of_comp V.val.ι W.ι (j V) (hj V)
  have hcover : (⋃ V : I, Set.range (Points.map (j V))) = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro y
    have hy : Points.map W.ι y ∈ W.pointsSet := ⟨y, rfl⟩
    obtain ⟨V, ⟨z, hz⟩, hV⟩ := (mem_targetLocus P f).mp hy
    refine ⟨⟨V, hV⟩, z, ?_⟩
    apply Points.map_injective_of_mono W.ι
    rw [← Points.map_comp, hj]
    exact hz
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (targetLocus_openCover_mem hτ j hjOpen hcover)
  rintro _ _ _ ⟨V⟩
  let a : pullback f V.val.ι ⟶ pullback f W.ι :=
    pullback.lift (pullback.fst f V.val.ι) (pullback.snd f V.val.ι ≫ j V)
      (by rw [Category.assoc, hj]; exact pullback.condition)
  have sq : IsPullback a (pullback.snd f V.val.ι)
      (pullback.snd f W.ι) (j V) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback f W.ι)
    · simpa only [a, pullback.lift_fst, hj] using
        IsPullback.of_hasPullback f V.val.ι
    · exact pullback.lift_snd _ _ _
  rw [← P.cancel_left_of_respectsIso sq.isoPullback.hom, sq.isoPullback_hom_snd]
  exact V.property

/-- A morphism occurring in a covering for the selected fppf, syntomic, smooth,
or étale precoverage factors through the target locus whenever the base change
has the target-local property. -/
theorem factorsThrough_targetLocus {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g)
    (hf : P (pullback.snd f g)) :
    ∃ χ : Y' ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = g := by
  obtain ⟨Q, rfl, hBC, hComp, hOpen, hMap⟩ := targetLocus_precoverage_spec hτ
  letI := hBC
  have hQg : Q g := by
    rw [← targetLocus_precoverage_morphismProperty Q hOpen]
    exact hg
  let U : OpenSubspace Y := OpenSubspace.fromOpens
    ⟨Set.range (Points.map g), (hMap g hQg).isOpen_range⟩
  let ψ : Y' ⟶ U.X := OpenSubspace.Construction.lift g (Set.Subset.refl _)
  have hψ : ψ ≫ U.ι = g := OpenSubspace.Construction.lift_ι _ _
  letI : IsOpenImmersion U.ι := U.isOpenImmersion
  have sqψ : IsPullback (𝟙 Y') ψ g U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hψ.symm⟩
  have hQψ : Q ψ := Q.of_isPullback sqψ hQg
  have hsurj : Function.Surjective (Points.map ψ) := by
    intro y
    have hy : Points.map U.ι y ∈ U.pointsSet := ⟨y, rfl⟩
    have hU : U.pointsSet = Set.range (Points.map g) :=
      OpenSubspace.fromOpens_pointsSet _
    rw [hU] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, Points.map_injective_of_mono U.ι ?_⟩
    rw [← Points.map_comp, hψ]
    exact hz
  have hcover : Presieve.ofArrows (fun _ : Unit ↦ Y') (fun _ ↦ ψ) ∈
      (precoverage Q).coverings U.X := by
    apply (ofArrows_mem_precoverage_iff Q _).mpr
    exact ⟨fun _ ↦ hQψ, Set.iUnion_eq_univ_iff.mpr fun y ↦ ⟨(), hsurj y⟩⟩
  have hU : P (pullback.snd f U.ι) := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hcover
    rintro _ _ _ ⟨i⟩
    let a : pullback f g ⟶ pullback f U.ι :=
      pullback.lift (pullback.fst f g) (pullback.snd f g ≫ ψ)
        (by rw [Category.assoc, hψ]; exact pullback.condition)
    have sq : IsPullback a (pullback.snd f g) (pullback.snd f U.ι) ψ := by
      apply IsPullback.of_right (t := IsPullback.of_hasPullback f U.ι)
      · simpa only [a, pullback.lift_fst, hψ] using IsPullback.of_hasPullback f g
      · exact pullback.lift_snd _ _ _
    rw [← P.cancel_left_of_respectsIso sq.isoPullback.hom, sq.isoPullback_hom_snd]
    exact hf
  obtain ⟨χ, hχ⟩ := targetLocus_maximal P f U hU
  exact ⟨ψ ≫ χ, by rw [Category.assoc, hχ, hψ]⟩

/-- The target locus of a target-local property commutes, on underlying point
sets, with base change by a morphism occurring in a covering for the selected
fppf, syntomic, smooth, or étale precoverage. -/
theorem targetLocus_inverseImage {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g) :
    (targetLocus P (pullback.snd f g)).pointsSet =
      Points.map g ⁻¹' (targetLocus P f).pointsSet := by
  obtain ⟨Q, rfl, hBC, hComp, hOpen, hMap⟩ := targetLocus_precoverage_spec hτ
  letI := hBC
  letI := hComp
  have hQg : Q g := by
    rw [← targetLocus_precoverage_morphismProperty Q hOpen]
    exact hg
  let f' := pullback.snd f g
  let W := targetLocus P f
  let W' := targetLocus P f'
  ext y
  constructor
  · intro hy
    have sq := (IsPullback.of_hasPullback f' W'.ι).paste_horiz
      (IsPullback.of_hasPullback f g)
    have hP : P (pullback.snd f (W'.ι ≫ g)) := by
      rw [← P.cancel_left_of_respectsIso sq.isoPullback.hom, sq.isoPullback_hom_snd]
      exact (targetLocus_isLargest P hτ f').1
    have hmem : (precoverage Q).morphismProperty (W'.ι ≫ g) := by
      rw [targetLocus_precoverage_morphismProperty Q hOpen]
      exact Q.comp_mem _ _ (hOpen _ W'.isOpenImmersion) hQg
    obtain ⟨χ, hχ⟩ := factorsThrough_targetLocus P hτ f (W'.ι ≫ g) hmem hP
    obtain ⟨z, rfl⟩ := hy
    exact ⟨Points.map χ z, by rw [← Points.map_comp, hχ, Points.map_comp]⟩
  · intro hy
    letI : IsOpenImmersion W.ι := W.isOpenImmersion
    let V := W.inverseImage g
    let ψ : V.X ⟶ W.X := restrictTo g W
    have sqV : IsPullback V.ι ψ g W.ι := openInverseImage_isPullback g W.ι
    have hmem : (precoverage Q).morphismProperty ψ := by
      rw [targetLocus_precoverage_morphismProperty Q hOpen]
      exact Q.of_isPullback sqV hQg
    let a : pullback f' V.ι ⟶ pullback f W.ι :=
      pullback.lift (pullback.fst f' V.ι ≫ pullback.fst f g)
        (pullback.snd f' V.ι ≫ ψ) (by
          rw [Category.assoc, pullback.condition, ← Category.assoc,
            pullback.condition, Category.assoc, sqV.w, ← Category.assoc])
    have sq : IsPullback a (pullback.snd f' V.ι) (pullback.snd f W.ι) ψ := by
      apply IsPullback.of_right (t := IsPullback.of_hasPullback f W.ι)
      · simpa only [a, pullback.lift_fst, sqV.w] using
          (IsPullback.of_hasPullback f' V.ι).paste_horiz
            (IsPullback.of_hasPullback f g)
      · exact pullback.lift_snd _ _ _
    have hV : P (pullback.snd f' V.ι) :=
      targetLocus_of_isPullback sq hmem (targetLocus_isLargest P hτ f).1
    refine (mem_targetLocus P f').mpr ⟨V, ?_, hV⟩
    change y ∈ (W.inverseImage g).pointsSet
    rw [OpenSubspace.inverseImage_pointsSet]
    exact hy

/-- For a property local on the target in the selected fppf, syntomic, smooth,
or étale topology, its target locus pulls back to the target locus along every
member of a covering family with an arbitrary index universe. -/
theorem targetLocus_inverseImage_cover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : Precoverage.ZeroHypercover.{v} K Y) (i : 𝒰.I₀) :
    (targetLocus P (pullback.snd f (𝒰.f i))).pointsSet =
      Points.map (𝒰.f i) ⁻¹' (targetLocus P f).pointsSet := by
  exact targetLocus_inverseImage P hτ f (𝒰.f i) (𝒰.morphismProperty i)

end AlgebraicGeometry.AlgebraicSpace
