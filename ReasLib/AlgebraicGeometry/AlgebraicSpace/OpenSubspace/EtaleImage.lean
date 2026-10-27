/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

/-!
# Étale images as open subspaces

An étale morphism from a scheme to an algebraic space factors through the open subspace
cut out by its image of points as a surjective étale morphism. The original kernel pair
remains a kernel pair of that lift, and the same relation presents the open image as `U/R`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Points

/-- The image of points of an étale morphism from a scheme is open in the canonical topology. -/
theorem isOpen_range_map_of_etale {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f) :
    IsOpen (Set.range (Points.map f)) := by
  have hrange : Set.range (Points.map f) = Set.range (mapOfOver f) := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, rfl⟩ := (ofOver.pointsEquiv U).surjective p
      exact ⟨q, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨ofOver.pointsEquiv U p, rfl⟩
  rw [hrange]
  exact (isOpenMap_mapOfOver f hf).isOpen_range

end Points

namespace OpenSubspace

private theorem inclusion_presheaf_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (X' : OpenSubspace X) : Mono (C := (Over S)ᵒᵖ ⥤ Type u) X'.ι := by
  apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms (C := Over S) X'.ι
  apply MorphismProperty.relative_monotone _ _ X'.isOpenImmersion.presheaf
  intro U V j hj
  letI : AlgebraicGeometry.IsOpenImmersion j.left := hj
  exact Over.mono_of_mono_left j

private theorem inclusion_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (X' : OpenSubspace X) : Mono X'.ι := by
  letI := inclusion_presheaf_mono X'
  exact ⟨fun {Z} g h e ↦ (cancel_mono (C := (Over S)ᵒᵖ ⥤ Type u) X'.ι).mp e⟩

private theorem etale_of_factorization {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (MorphismProperty.over (@Etale)).presheaf f' := by
  letI := inclusion_presheaf_mono X'
  letI : (MorphismProperty.over (@Etale) (X := S)).RespectsIso := by
    rw [MorphismProperty.over_eq_inverseImage]
    infer_instance
  have hfac' : CategoryStruct.comp (obj := (Over S)ᵒᵖ ⥤ Type u) f' X'.ι = f := hfac
  apply MorphismProperty.relative.of_exists
  intro T p
  have hpb := hf.rep.isPullback (p ≫ X'.ι)
  have hcomm : hf.rep.fst (p ≫ X'.ι) ≫ f' =
      yoneda.map (hf.rep.snd (p ≫ X'.ι)) ≫ p := by
    apply (cancel_mono (C := (Over S)ᵒᵖ ⥤ Type u) X'.ι).mp
    simpa only [Category.assoc, hfac'] using hpb.w
  refine ⟨hf.rep.pullback (p ≫ X'.ι), hf.rep.fst (p ≫ X'.ι),
    hf.rep.snd (p ≫ X'.ι), ?_, hf.property_snd (p ≫ X'.ι)⟩
  have hbase : IsPullback p (𝟙 (yoneda.obj T)) X'.ι (p ≫ X'.ι) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  exact IsPullback.of_bot (by simpa only [Category.comp_id, hfac'] using hpb) hcomm hbase

private theorem surjective_points_of_factorization {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} {f : ofOver U ⟶ X}
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Function.Surjective (Points.map f') := by
  letI : Mono X'.ι := inclusion_mono X'
  intro x
  have hx : Points.map X'.ι x ∈ Set.range (Points.map f) := by
    rw [← hX']
    exact ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := hx
  refine ⟨u, Points.map_injective_of_mono X'.ι ?_⟩
  rw [← Points.map_comp, hfac, hu]

/-- There is an open subspace whose underlying points are the image of an étale morphism from a
scheme. -/
theorem exists_of_etale {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f) :
    ∃ X' : OpenSubspace X, X'.pointsSet = Set.range (Points.map f) := by
  exact ⟨fromOpens ⟨_, Points.isOpen_range_map_of_etale hf⟩, fromOpens_pointsSet _⟩

/-- An étale morphism from a scheme factors through the open subspace on its image of points as a
surjective étale morphism. -/
theorem exists_surjective_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f)) :
    ∃ f' : ofOver U ⟶ X'.X, f' ≫ X'.ι = f ∧
      (MorphismProperty.over (@Etale)).presheaf f' ∧
        (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f' := by
  obtain ⟨f', hfac⟩ := (exists_lift_iff_range_subset X' f).mpr (by
    rw [hX'])
  exact ⟨f', hfac, etale_of_factorization hf X' hfac,
    ofOver_presheaf_surjective_of_map (surjective_points_of_factorization X' hX' hfac)⟩

/-- Factorization of an étale morphism from a scheme through the open subspace on its image of
points is unique. -/
theorem existsUnique_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f)) :
    ∃! f' : ofOver U ⟶ X'.X, f' ≫ X'.ι = f := by
  letI : Mono X'.ι := inclusion_mono X'
  obtain ⟨f', hfac, _, _⟩ := exists_surjective_etale_lift hf X' hX'
  exact ⟨f', hfac, fun g hg ↦ (cancel_mono X'.ι).mp (hg.trans hfac.symm)⟩

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is étale. -/
theorem etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (MorphismProperty.over (@Etale)).presheaf f' := by
  exact etale_of_factorization hf X' hfac

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is representably surjective. -/
theorem surjective_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f' := by
  exact ofOver_presheaf_surjective_of_map (surjective_points_of_factorization X' hX' hfac)

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is surjective on points. -/
theorem surjective_points_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Function.Surjective (Points.map f') := by
  exact surjective_points_of_factorization X' hX' hfac

/-- Any factorization of an étale morphism from a scheme through the open subspace on its image of
points is étale-locally surjective. -/
theorem locallySurjective_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f' := by
  have he := etale_lift hf X' hX' hfac
  have hs := surjective_lift hf X' hX' hfac
  constructor
  intro T s
  let p : yoneda.obj T ⟶ X'.X.functorOfPoints := yonedaEquiv.symm s
  let q : he.rep.pullback p ⟶ T := he.rep.snd p
  haveI : AlgebraicGeometry.Etale q.left := he.property_snd p
  haveI : AlgebraicGeometry.Surjective q.left :=
    hs.property p _ _ (he.rep.isPullback p)
  have hcover : Sieve.ofArrows (fun _ : Unit ↦ he.rep.pullback p) (fun _ ↦ q) ∈
      (Scheme.etaleTopology.over S) T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    apply (Scheme.ofArrows_mem_precoverage_iff _).mpr
    exact ⟨fun x ↦ ⟨(), AlgebraicGeometry.Surjective.surj (f := q.left) x⟩,
      fun _ ↦ inferInstance⟩
  apply (Scheme.etaleTopology.over S).superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro V g ⟨i⟩
  refine ⟨yonedaEquiv (he.rep.fst p), ?_⟩
  simpa only [← yonedaEquiv_comp, ← yonedaEquiv_naturality,
    p, Equiv.apply_symm_apply] using congrArg yonedaEquiv (he.rep.isPullback p).w

/-- The represented kernel pair of an étale morphism from a scheme remains a kernel pair of any
factorization through the open subspace on its image of points. -/
theorem isKernelPair_etale_lift {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : yoneda.obj U ⟶ X'.X.functorOfPoints} (hfac : f' ≫ X'.ι = f) :
    IsKernelPair f' (yoneda.map (kernelPair f hf.rep).t)
      (yoneda.map (kernelPair f hf.rep).s) := by
  letI := inclusion_presheaf_mono X'
  apply IsKernelPair.cancel_right_of_mono (C := (Over S)ᵒᵖ ⥤ Type u) (f₂ := X'.ι)
  rw [hfac]
  change IsKernelPair (C := (Over S)ᵒᵖ ⥤ Type u) f
    (yoneda.map (Limits.prod.lift (hf.rep.fst' f) (hf.rep.snd f) ≫ Limits.prod.fst))
    (yoneda.map (Limits.prod.lift (hf.rep.fst' f) (hf.rep.snd f) ≫ Limits.prod.snd))
  simpa only [IsKernelPair, ofOver_functorOfPoints, Limits.prod.lift_fst, Limits.prod.lift_snd]
    using hf.rep.isPullback' f

/-- The presentation of the open étale image by the original scheme atlas and the represented
kernel pair `R = U ×_X U`. -/
noncomputable def presentation {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    Presentation X'.X where
  U := U
  R := kernelPair f hf.rep
  atlas := f'
  isEtaleEquivalence := (Presentation.atlasRelation_spec f hf).1
  atlas_etale := etale_lift hf X' hX' hfac
  atlas_locallySurjective := locallySurjective_lift hf X' hX' hfac
  isKernelPair := isKernelPair_etale_lift hf X' hX' hfac

/-- The presentation of the open étale image is `X' = U/R` for the original scheme `U` and
the represented kernel pair `R = U ×_X U`. -/
theorem presentation_spec {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    {f : ofOver U ⟶ X} (hf : (MorphismProperty.over (@Etale)).presheaf f)
    (X' : OpenSubspace X) (hX' : X'.pointsSet = Set.range (Points.map f))
    {f' : ofOver U ⟶ X'.X} (hfac : f' ≫ X'.ι = f) :
    (presentation hf X' hX' hfac).U = U ∧
      (presentation hf X' hX' hfac).R = kernelPair f hf.rep ∧
        (presentation hf X' hX' hfac).atlas = f' := by
  exact ⟨rfl, rfl, rfl⟩

end OpenSubspace

end AlgebraicGeometry.AlgebraicSpace
