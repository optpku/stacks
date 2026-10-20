/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.AtlasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-! # The algebraic space of a reduced closed image

The relative image sheaf has a representable diagonal and a surjective étale atlas given by
the reduced closed subscheme of the ambient atlas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Space

open ReducedClosed.AtlasImage

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))

/-- The target sheaf's actual inclusion as a natural transformation. -/
abbrev inclusionNat := (inclusion X Z).hom

/-- The atlas map as a natural transformation with the already specified carrier. -/
abbrev atlasNat := (toImage X Z).hom

variable {T : Over S} (g : yoneda.obj T ⟶ (imageSheaf X Z).obj)

/-- The pullback of the ambient étale atlas along the test morphism to the image sheaf. -/
def testScheme : Over S :=
  (AtlasInput.representableEtale X).rep.pullback (g ≫ inclusionNat X Z)

/-- The projection from the test pullback to the ambient atlas. -/
def testToInputAtlas : testScheme X Z g ⟶ atlasScheme X :=
  (AtlasInput.representableEtale X).rep.fst' (g ≫ inclusionNat X Z)

/-- The projection from the test pullback to the test scheme. -/
def testToBase : testScheme X Z g ⟶ T :=
  (AtlasInput.representableEtale X).rep.snd (g ≫ inclusionNat X Z)

/-- The two test pullback projections have the same composite into the ambient space. -/
theorem test_commutes :
    (yoneda.map (testToBase X Z g) ≫ g) ≫ inclusionNat X Z =
      yoneda.map (testToInputAtlas X Z g) ≫ atlasMap X := by
  exact ((AtlasInput.representableEtale X).rep.isPullback'
    (g ≫ inclusionNat X Z)).w.symm

/-- The actual map into image ×_X U. -/
def testToPullback : yoneda.obj (testScheme X Z g) ⟶
    ReducedClosed.AtlasPullback.pullbackPresheaf X Z :=
  pullback.lift (yoneda.map (testToBase X Z g) ≫ g)
    (yoneda.map (testToInputAtlas X Z g)) (test_commutes X Z g)

/-- Recover the morphism into the concrete reduced atlas by the fixed inverse. -/
def testToReduced : testScheme X Z g ⟶ reducedAtlas X Z :=
  yoneda.preimage (testToPullback X Z g ≫ (ReducedClosed.AtlasPullback.comparisonIso X Z).inv)

/-- The test scheme represents the pullback of the reduced atlas to the test scheme. -/
theorem test_isPullback :
    IsPullback (yoneda.map (testToReduced X Z g)) (yoneda.map (testToBase X Z g))
      (atlasNat X Z) g := by
  sorry

/-- The test pullback projection is étale as a base change of the ambient atlas. -/
theorem testToBase_etale : AlgebraicGeometry.Etale (testToBase X Z g).left :=
  (AtlasInput.representableEtale X).property
    (g ≫ inclusionNat X Z)
    (yoneda.map (testToInputAtlas X Z g)) (testToBase X Z g)
    ((AtlasInput.representableEtale X).rep.isPullback'
      (g ≫ inclusionNat X Z))

/-- The reduced atlas morphism to its image sheaf is representable by schemes. -/
theorem atlas_representable : yoneda.relativelyRepresentable (atlasNat X Z) := by
  intro T g
  exact ⟨testScheme X Z g, testToBase X Z g, yoneda.map (testToReduced X Z g),
    test_isPullback X Z g⟩

/-- Any other represented square is isomorphic over its base to the
displayed testScheme square, whose projection is the original étale map. -/
theorem atlas_etale :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasNat X Z) := by
  refine ⟨atlas_representable X Z, ?_⟩
  intro T V g a b hb
  sorry

/-- Relative image gives fppf-local surjectivity, and the displayed atlas is
étale. An étale surjective morphism is locally surjective for the étale
topology. This is a covering property of the fixed map. -/
theorem atlas_surjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlasNat X Z) := by
  sorry

/-- The image inclusion is literally monic on its presheaf carrier. -/
instance inclusionNat_mono : Mono (inclusionNat X Z) := by
  change Mono ((sheafToPresheaf _ _).map (inclusion X Z))
  infer_instance

/-- Pullback squares can be cancelled through this fixed monomorphism. -/
theorem cancel_image_square {A B C : (Over S)ᵒᵖ ⥤ Type u}
    (a : C ⟶ A) (b : C ⟶ B) (p : A ⟶ (imageSheaf X Z).obj)
    (q : B ⟶ (imageSheaf X Z).obj)
    (h : IsPullback a b (p ≫ inclusionNat X Z) (q ≫ inclusionNat X Z)) :
    IsPullback a b p q := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfFactors
    (p ≫ inclusionNat X Z) (q ≫ inclusionNat X Z) (inclusionNat X Z)
    p q rfl rfl h.cone h.isLimit)

/-- The original X-diagonal represents all scheme-to-image fibre products:
postcompose into X and cancel the actual mono image inclusion. -/
theorem mapFromScheme_representable {T : Over S}
    (g : yoneda.obj T ⟶ (imageSheaf X Z).obj) : yoneda.relativelyRepresentable g := by
  intro V h
  let rep := Functor.relativelyRepresentable.of_diag X.representableDiagonal
    (g ≫ inclusionNat X Z)
  exact ⟨rep.pullback (h ≫ inclusionNat X Z), rep.snd (h ≫ inclusionNat X Z),
    rep.fst (h ≫ inclusionNat X Z),
    cancel_image_square X Z _ _ g h (rep.isPullback (h ≫ inclusionNat X Z))⟩

/-- The diagonal of the image sheaf is representable by schemes. -/
theorem diagonal_representable :
    yoneda.relativelyRepresentable (Limits.diag (imageSheaf X Z).obj) :=
  Functor.relativelyRepresentable.diag_of_map_from_obj
    (fun {_} g ↦ mapFromScheme_representable X Z g)

/-- The algebraic space whose functor of points is the image of the reduced atlas. -/
def space : AlgebraicSpace S :=
  AlgebraicSpace.ofFunctor (imageSheaf X Z).obj
    (image_isSheaf X Z) (diagonal_representable X Z)
    ⟨reducedAtlas X Z, atlasNat X Z, atlas_etale X Z, atlas_surjective X Z⟩

/-- The inclusion retains the actual image-subtype function. -/
def ι : space X Z ⟶ X := inclusionNat X Z

/-- The functor of points of the reduced closed space is the relative image sheaf. -/
@[simp]
theorem carrier_eq : (space X Z).functorOfPoints = (imageSheaf X Z).obj := rfl

/-- The actual reduced atlas has the same image after packaging as a space. -/
def chart : ofOver (reducedAtlas X Z) ⟶ space X Z := atlasNat X Z

/-- The reduced atlas chart followed by the image inclusion is the ambient chart map. -/
theorem chart_ι : chart X Z ≫ ι X Z = chartMap X Z :=
  congrArg (fun h ↦ h.hom) (factorization X Z)

/-- The closed subscheme defined by the radical vanishing ideal on the atlas is reduced. -/
theorem reducedAtlas_reduced : AlgebraicGeometry.IsReduced (reducedAtlas X Z).left := by
  sorry

/-- The reduced closed image algebraic space is reduced on its surjective étale atlas. -/
instance space_reduced : AlgebraicSpace.IsReduced (space X Z) where
  exists_reduced_etaleCover := ⟨reducedAtlas X Z, chart X Z,
    atlas_etale X Z, atlas_surjective X Z, reducedAtlas_reduced X Z⟩

end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Space

