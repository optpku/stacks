/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.PairQuotient

/-!
# Explicit pullback witnesses for the relative-spectrum atlas

The pullback of the actual spectrum atlas along an original algebra point is
the supplied base-atlas pullback. Its maps are the concrete local spectrum
lift and test projection. The limiting cone lifts by the actual represented
base-atlas pullback, with no unspecified representing scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The concrete local atlas lift recovers the given original algebra point. -/
theorem relativeSpectrumPointAtlasLift_toFunctor (A : X.QcAlgebraUnder)
    (p : relativeSpectrumPair A T) :
    yoneda.map (relativeSpectrumPointAtlasLift A p) ≫ relativeSpectrumAtlasNat A =
      yoneda.map (relativeSpectrumPointAtlasToTest A p) ≫ yonedaEquiv.symm p := sorry

/-- The concrete pullback cone for the atlas along an original relative-spectrum point. -/
def relativeSpectrumAtlasPointPullbackCone (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    PullbackCone (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p) :=
  PullbackCone.mk (yoneda.map (relativeSpectrumPointAtlasLift A p))
    (yoneda.map (relativeSpectrumPointAtlasToTest A p))
    (relativeSpectrumPointAtlasLift_toFunctor A p)

/-- Project every original spectrum point to its specified base point. -/
def relativeSpectrumFunctorToX (A : X.QcAlgebraUnder) : relativeSpectrumFunctor A ⟶ X.functorOfPoints where
  app T := TypeCat.ofHom fun p ↦ p.1
  naturality := by
    intro T T' f
    ext p
    change yonedaEquiv (yoneda.map f.unop ≫ yonedaEquiv.symm p.1) =
      X.functorOfPoints.map f p.1
    simpa only [Quiver.Hom.op_unop, Equiv.apply_symm_apply] using
      (yonedaEquiv_naturality (yonedaEquiv.symm p.1) f.unop).symm

/-- The actual atlas point transformation projects to its actual structural map to X. -/
theorem relativeSpectrumAtlasNat_toBase (A : X.QcAlgebraUnder) :
    relativeSpectrumAtlasNat A ≫ relativeSpectrumFunctorToX A = relativeSpectrumDescentAtlasToX A := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, relativeSpectrumAtlasNat_yoneda]
  exact relativeSpectrumAtlasPoint_base A

/-- The original point transformation projects to the supplied original base arrow. -/
theorem relativeSpectrumPointNat_toBase (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    yonedaEquiv.symm p ≫ relativeSpectrumFunctorToX A = relativeSpectrumPointBase A p := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact (Equiv.apply_symm_apply yonedaEquiv p.1).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual mediating natural transformation into the represented base-atlas pullback. -/
def relativeSpectrumAtlasPointPullbackLift (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T)
    (c : PullbackCone (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p)) :
    c.pt ⟶ yoneda.obj (relativeSpectrumPointAtlasOver A p) :=
  ((atlasHom_presheaf_etale X).rep.isPullback (relativeSpectrumPointBase A p)).lift
    (c.fst ≫ yoneda.map
      (Over.homMk (Scheme.relativeSpectrumOver
        (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl))
    c.snd (by
      simpa only [Category.assoc, relativeSpectrumAtlasNat_toBase,
        relativeSpectrumPointNat_toBase, relativeSpectrumDescentAtlasToX] using
        congrArg (fun f ↦ f ≫ relativeSpectrumFunctorToX A) c.condition)

set_option backward.isDefEq.respectTransparency false in
/-- The point-atlas pullback cone has the real represented-pullback lift operation. -/
def relativeSpectrumAtlasPointPullbackIsLimit (A : X.QcAlgebraUnder) (p : relativeSpectrumPair A T) :
    IsLimit (relativeSpectrumAtlasPointPullbackCone A p) :=
  PullbackCone.IsLimit.mk (relativeSpectrumPointAtlasLift_toFunctor A p)
    (relativeSpectrumAtlasPointPullbackLift A p) sorry
    (by
      intro c
      exact ((atlasHom_presheaf_etale X).rep.isPullback
        (relativeSpectrumPointBase A p)).lift_snd _ _ _)
    (by
      intro c m hfst hsnd
      have hπ : relativeSpectrumPointAtlasLift A p ≫
          Over.homMk (Scheme.relativeSpectrumOver
            (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl =
          relativeSpectrumPointAtlasToAtlas A p := by
        apply Over.OverMorphism.ext
        exact Scheme.relativeSpectrumPointMap_toBase _ _
      have hmap : yoneda.map (relativeSpectrumPointAtlasLift A p) ≫
          yoneda.map (Over.homMk (Scheme.relativeSpectrumOver
            (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl) =
          (atlasHom_presheaf_etale X).rep.fst (relativeSpectrumPointBase A p) := by
        rw [← yoneda.map_comp, hπ]
        exact (atlasHom_presheaf_etale X).rep.map_fst' _
      apply ((atlasHom_presheaf_etale X).rep.isPullback
        (relativeSpectrumPointBase A p)).hom_ext
      · change m ≫ _ = relativeSpectrumAtlasPointPullbackLift A p c ≫ _
        calc
          m ≫ (atlasHom_presheaf_etale X).rep.fst (relativeSpectrumPointBase A p) =
              c.fst ≫ yoneda.map (Over.homMk (Scheme.relativeSpectrumOver
                (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π rfl) := by
            rw [← hmap, ← Category.assoc, hfst]
          _ = relativeSpectrumAtlasPointPullbackLift A p c ≫
              (atlasHom_presheaf_etale X).rep.fst (relativeSpectrumPointBase A p) :=
            (((atlasHom_presheaf_etale X).rep.isPullback
              (relativeSpectrumPointBase A p)).lift_fst _ _ _).symm
      · change m ≫ _ = relativeSpectrumAtlasPointPullbackLift A p c ≫ _
        exact hsnd.trans (((atlasHom_presheaf_etale X).rep.isPullback
          (relativeSpectrumPointBase A p)).lift_snd _ _ _).symm)

/-- The actual atlas has explicit representing schemes and both projection maps for every test point. -/
theorem relativeSpectrumAtlasNat_relativelyRepresentable (A : X.QcAlgebraUnder) :
    yoneda.relativelyRepresentable (relativeSpectrumAtlasNat A) := by
  intro T g
  let p : relativeSpectrumPair A T := yonedaEquiv g
  refine ⟨relativeSpectrumPointAtlasOver A p, relativeSpectrumPointAtlasToTest A p,
    yoneda.map (relativeSpectrumPointAtlasLift A p), ?_⟩
  have hp := IsPullback.of_isLimit (relativeSpectrumAtlasPointPullbackIsLimit A p)
  change IsPullback (yoneda.map (relativeSpectrumPointAtlasLift A p))
    (yoneda.map (relativeSpectrumPointAtlasToTest A p))
    (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p) at hp
  simpa only [p, Equiv.symm_apply_apply] using hp

/-- The concrete atlas is representably étale by its stored-atlas pullback projections. -/
theorem relativeSpectrumAtlasNat_presheaf_etale (A : X.QcAlgebraUnder) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (relativeSpectrumAtlasNat A) := by
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage (@AlgebraicGeometry.Etale) (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro T g
  let p : relativeSpectrumPair A T := yonedaEquiv g
  refine ⟨relativeSpectrumPointAtlasOver A p, yoneda.map (relativeSpectrumPointAtlasLift A p),
    relativeSpectrumPointAtlasToTest A p, ?_, ?_⟩
  · show IsPullback _ _ _ g
    have hp := IsPullback.of_isLimit (relativeSpectrumAtlasPointPullbackIsLimit A p)
    change IsPullback (yoneda.map (relativeSpectrumPointAtlasLift A p))
      (yoneda.map (relativeSpectrumPointAtlasToTest A p))
      (relativeSpectrumAtlasNat A) (yonedaEquiv.symm p) at hp
    simpa only [p, Equiv.symm_apply_apply] using hp
  · change AlgebraicGeometry.Etale (relativeSpectrumPointAtlasToTest A p).left
    exact (atlasHom_presheaf_etale X).property (relativeSpectrumPointBase A p) _ _
      ((atlasHom_presheaf_etale X).rep.isPullback (relativeSpectrumPointBase A p))

/-- The concrete atlas covers the original spectrum-point functor in the étale topology. -/
theorem relativeSpectrumAtlasNat_locallySurjective (A : X.QcAlgebraUnder) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (relativeSpectrumAtlasNat A) := by
  refine ⟨fun {T} p ↦ ?_⟩
  have hlocal : Presheaf.imageSieve (relativeSpectrumAtlasNat A) p
      (relativeSpectrumPointAtlasToTest A p) := by
    refine ⟨relativeSpectrumPointAtlasLift A p, ?_⟩
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_symm_app_apply] using
      congrArg yonedaEquiv (relativeSpectrumPointAtlasLift_toFunctor A p)
  apply (Scheme.etaleTopology.over S).superset_covering ?_ (relativeSpectrumPointAtlasCover_mem A p)
  intro W f hf
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
  exact Sieve.downward_closed _ hlocal a

end AlgebraicGeometry.AlgebraicSpace
