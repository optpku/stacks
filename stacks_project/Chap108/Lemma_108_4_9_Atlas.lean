module

public import stacks_project.Chap108.Lemma_108_4_9_SchemeEtaleModules
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import stacks_project.Chap66.Definition_66_18_1_Site

/-! An actual atlas and chart functor extracted from the given algebraic space. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {S : Scheme.{u}}

private instance etaleOverComp :
    (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderComposition :=
  inferInstanceAs ((MorphismProperty.inverseImage (@AlgebraicGeometry.Etale)
    (Over.forget S)).IsStableUnderComposition)

private instance etaleOverBaseChange :
    (MorphismProperty.over (@AlgebraicGeometry.Etale) (X := S)).IsStableUnderBaseChange where
  of_isPullback h hg :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (h.map (Over.forget S)) hg

/-- This scheme is selected from the atlas field of the input, not a new existence axiom. -/
noncomputable def atlasScheme (X : AlgebraicSpace S) : Over S := X.atlas.choose

/-- The actual atlas morphism supplied by the input's defining condition. -/
noncomputable def atlasMap (X : AlgebraicSpace S) :
    yoneda.obj (atlasScheme X) ⟶ X.functorOfPoints := X.atlas.choose_spec.choose

/-- Representable etaleness of this specific atlas. -/
theorem atlasMapEtale (X : AlgebraicSpace S) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasMap X) :=
  X.atlas.choose_spec.choose_spec.1

/-- Local surjectivity of this specific atlas. -/
theorem atlasMapSurjective (X : AlgebraicSpace S) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlasMap X) :=
  X.atlas.choose_spec.choose_spec.2

/-- Representable etaleness implies the existing algebraic-space etale predicate. -/
theorem spaceEtale_of_presheaf {U : Over S} {X : AlgebraicSpace S}
    (p : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X)
    (hp : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf p) :
    AlgebraicGeometry.AlgebraicSpace.Etale p where
  of_etale q hq :=
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem q p hq hp

/-- The original site predicate gives representable etaleness by testing the identity chart. -/
theorem presheaf_of_spaceEtale {U : Over S} {X : AlgebraicSpace S}
    (p : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X)
    (hp : AlgebraicGeometry.AlgebraicSpace.Etale p) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf p := by
  have hid : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      (𝟙 (yoneda.obj U)) := by
    have h : (MorphismProperty.over (@AlgebraicGeometry.Etale)) (𝟙 U) :=
      inferInstanceAs (AlgebraicGeometry.Etale (𝟙 U.left))
    simpa only [CategoryTheory.Functor.map_id] using
      (MorphismProperty.relative_map (F := yoneda) h)
  simpa only [Category.id_comp] using! hp.of_etale (𝟙 (yoneda.obj U)) hid

/-- The atlas itself is an object of the actual algebraic-space small etale site. -/
noncomputable def atlasSiteObject (X : AlgebraicSpace S) :
    AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ (atlasMap X)
    (spaceEtale_of_presheaf (atlasMap X) (atlasMapEtale X))

/-- Forget an etale chart of the atlas scheme to a scheme over the original base. -/
noncomputable def atlasUnderlying (X : AlgebraicSpace S) : (atlasScheme X).left.Etale ⥤ Over S where
  obj W := Over.mk (W.hom ≫ (atlasScheme X).hom)
  map {A B} f := Over.homMk f.left (by
    have h : f.left ≫ B.hom = A.hom := by simpa using f.w
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ (atlasScheme X).hom) h))

/-- The map from an etale chart back to the atlas, over the original base. -/
noncomputable def chartToAtlas (X : AlgebraicSpace S) (W : (atlasScheme X).left.Etale) :
    (atlasUnderlying X).obj W ⟶ atlasScheme X := Over.homMk W.hom rfl

/-- The actual chart map to the input space. -/
noncomputable def chartMap (X : AlgebraicSpace S) (W : (atlasScheme X).left.Etale) :
    yoneda.obj ((atlasUnderlying X).obj W) ⟶ X.functorOfPoints :=
  yoneda.map (chartToAtlas X W) ≫ atlasMap X

/-- These chart maps are representable etale morphisms. -/
theorem chartMapEtale (X : AlgebraicSpace S) (W : (atlasScheme X).left.Etale) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (chartMap X W) := by
  apply (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem
  · exact MorphismProperty.relative_map (F := yoneda) (P := MorphismProperty.over
      (@AlgebraicGeometry.Etale)) W.prop
  · exact atlasMapEtale X

/-- The original site's object defined by each chart map. -/
noncomputable def chartSiteObject (X : AlgebraicSpace S) (W : (atlasScheme X).left.Etale) :
    AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ (chartMap X W)
    (spaceEtale_of_presheaf (chartMap X W) (chartMapEtale X W))

/-- The triangle from a chart to the atlas commutes under an actual etale-site map. -/
theorem chartToAtlas_natural (X : AlgebraicSpace S)
    {A B : (atlasScheme X).left.Etale} (f : A ⟶ B) :
    (atlasUnderlying X).map f ≫ chartToAtlas X B = chartToAtlas X A := by
  apply Over.OverMorphism.ext
  exact MorphismProperty.Over.w f

/-- The corresponding triangle to the input algebraic space commutes. -/
theorem chartMap_natural (X : AlgebraicSpace S)
    {A B : (atlasScheme X).left.Etale} (f : A ⟶ B) :
    yoneda.map ((atlasUnderlying X).map f) ≫ chartMap X B = chartMap X A := by
  change yoneda.map ((atlasUnderlying X).map f) ≫
    (yoneda.map (chartToAtlas X B) ≫ atlasMap X) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, chartToAtlas_natural]
  rfl

/-- The actual chart functor from the scheme atlas to the original small etale site. -/
noncomputable def atlasEtaleFunctor (X : AlgebraicSpace S) :
    (atlasScheme X).left.Etale ⥤ AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X where
  obj := chartSiteObject X
  map f := MorphismProperty.CostructuredArrow.homMk ((atlasUnderlying X).map f) trivial
    (chartMap_natural X f)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact (atlasUnderlying X).map_id A
  map_comp f g := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    exact (atlasUnderlying X).map_comp f g

/-- A genuinely u-small affine chart family in the original site of the input space. -/
noncomputable def spaceAffineInclusion (X : AlgebraicSpace S) :
    SchemeAffineIndex (atlasScheme X).left ⥤ AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X :=
  schemeAffineInclusion (atlasScheme X).left ⋙ atlasEtaleFunctor X

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
