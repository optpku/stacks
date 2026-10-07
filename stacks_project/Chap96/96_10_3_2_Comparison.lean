module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap96.«96_10_3_1_Comparison»

/-!
# Inverse-image comparison of small étale sheaves of algebraic spaces

A 2-commutative triangle of 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf`, with legs represented by algebraic spaces `U` and `V`, induces
the comparison morphism
`a_small⁻¹(g⁻¹ F|_{V_étale}) ⟶ f⁻¹ F|_{U_étale}`
as the sheaf-adjunction adjunct of the restricted unit of `a⁻¹ ⊣ a_*` after
2-cell transport and the big/small identification of `96.10.3.1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of étale topoi induced by a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. -/
abbrev etaleMorphismOfTopoi {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn Z.etaleTopology Y.etaleTopology :=
  (toCartesianBasedFunctor h).morphismOfTopoiIn (StandardTopology.etale.overTopology S)

/-- Inverse image of étale sheaves along a 1-morphism of categories fibred in
groupoids, i.e. `h⁻¹`. -/
abbrev etaleInverseImage {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf Z.etaleTopology (Type (u + 1)) ⥤ Sheaf Y.etaleTopology (Type (u + 1)) :=
  (etaleMorphismOfTopoi h).inverseImage

/-- Direct image of étale sheaves along a 1-morphism of categories fibred in
groupoids, i.e. `h_*`. -/
abbrev etaleDirectImage {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf Y.etaleTopology (Type (u + 1)) ⥤ Sheaf Z.etaleTopology (Type (u + 1)) :=
  (etaleMorphismOfTopoi h).pushforward

/-- `etaleInverseImage` is the inverse image of `etaleMorphismOfTopoi`. -/
theorem etaleInverseImage_eq {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage h = (etaleMorphismOfTopoi h).inverseImage :=
  sorry

/-- `etaleDirectImage` is the direct image of `etaleMorphismOfTopoi`. -/
theorem etaleDirectImage_eq {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleDirectImage h = (etaleMorphismOfTopoi h).pushforward :=
  sorry

/-- The total functor of a 1-morphism of groupoid fibrations is continuous for
the associated étale topologies. -/
instance toFunctor_etale_isContinuous {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toFunctor h).IsContinuous Y.etaleTopology Z.etaleTopology :=
  sorry

/-- The total functor of a 1-morphism of groupoid fibrations is cocontinuous for
the associated étale topologies. -/
instance toFunctor_etale_isCocontinuous {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toFunctor h).IsCocontinuous Y.etaleTopology Z.etaleTopology :=
  sorry

/-- The cartesian total functor is continuous for the associated étale topologies. -/
instance cartesianToFunctor_etale_isContinuous {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toCartesianBasedFunctor h).toFunctor.IsContinuous Y.etaleTopology Z.etaleTopology :=
  sorry

/-- Composite total functors are continuous for associated étale topologies. -/
instance toFunctor_comp_etale_isContinuous {Y Z W : GroupoidsOver S}
    (h : Y ⟶ Z) (k : Z ⟶ W) :
    (toFunctor h ⋙ toFunctor k).IsContinuous Y.etaleTopology W.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    Y.etaleTopology Z.etaleTopology W.etaleTopology

/-- The cartesian total functor agrees with `toFunctor`. -/
theorem cartesian_toFunctor_eq {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toCartesianBasedFunctor h).toFunctor = toFunctor h :=
  congrArg (fun F => F.toFunctor) (toCartesianBasedFunctor.toBasedFunctor h)

/-- The canonical comparison from cocontinuous inverse image to continuous
sheaf pushforward along the underlying total functor. -/
abbrev etaleInverseImageComparison {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [HasWeakSheafify Z.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage h ⟶
      (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous (Type (u + 1))
        Y.etaleTopology Z.etaleTopology :=
  CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison
    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)

/-- Continuous sheaf pushforward along the cartesian total functor compared with
pushforward along `toFunctor`. -/
def etaleContinuousPushforwardIso {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous (Type (u + 1))
        Y.etaleTopology Z.etaleTopology ≅
      (toFunctor h).sheafPushforwardContinuous (Type (u + 1))
        Y.etaleTopology Z.etaleTopology :=
  sheafPushforwardContinuousIso (eqToIso (cartesian_toFunctor_eq h))
    (Type (u + 1)) Y.etaleTopology Z.etaleTopology

/-- An isomorphism `t : h ≅ k` of 1-morphisms induces `h⁻¹ ≅ k⁻¹` of étale
inverse images. -/
def etaleInverseImageIso {Y Z : GroupoidsOver S} {h k : Y ⟶ Z} (t : h ≅ k)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [HasWeakSheafify Z.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage h ≅ etaleInverseImage k :=
  asIso (etaleInverseImageComparison h) ≪≫
    etaleContinuousPushforwardIso h ≪≫
      sheafPushforwardContinuousIso (toFunctorIso t) (Type (u + 1))
        Y.etaleTopology Z.etaleTopology ≪≫
        (etaleContinuousPushforwardIso k).symm ≪≫
          (asIso (etaleInverseImageComparison k)).symm

/-- Inverse image of a composite 1-morphism compares with the composite of
inverse images. -/
def etaleInverseImage_compIso {Y Z W : GroupoidsOver S} (h : Y ⟶ Z) (k : Z ⟶ W)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [HasSheafify Z.etaleTopology (Type (u + 1))]
    [HasWeakSheafify Z.etaleTopology (Type (u + 1))]
    [HasWeakSheafify W.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Z.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor (h ≫ k)).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage (h ≫ k) ≅ etaleInverseImage k ⋙ etaleInverseImage h :=
  asIso (etaleInverseImageComparison (h ≫ k)) ≪≫
    etaleContinuousPushforwardIso (h ≫ k) ≪≫
      sheafPushforwardContinuousIso
          (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).symm (Type (u + 1))
          Y.etaleTopology W.etaleTopology ≪≫
        (sheafPushforwardContinuousComp (toFunctor h) (toFunctor k) (Type (u + 1))
            Y.etaleTopology Z.etaleTopology W.etaleTopology).symm ≪≫
          isoWhiskerRight (etaleContinuousPushforwardIso k).symm
              ((toFunctor h).sheafPushforwardContinuous (Type (u + 1))
                Y.etaleTopology Z.etaleTopology) ≪≫
            isoWhiskerRight (asIso (etaleInverseImageComparison k)).symm
                ((toFunctor h).sheafPushforwardContinuous (Type (u + 1))
                  Y.etaleTopology Z.etaleTopology) ≪≫
              isoWhiskerLeft (etaleInverseImage k) (etaleContinuousPushforwardIso h).symm ≪≫
                isoWhiskerLeft (etaleInverseImage k)
                  (asIso (etaleInverseImageComparison h)).symm

variable {X : GroupoidsOver S}
variable {U V : AlgebraicSpace S} (a : U ⟶ V)
variable (f : U.toGroupoids ⟶ X) (g : V.toGroupoids ⟶ X)
variable (φ : toGroupoids.map a ≫ g ≅ f)
variable [HasSheafify U.toGroupoids.etaleTopology (Type (u + 1))]
variable [HasSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify V.toGroupoids.etaleTopology (Type (u + 1))]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : V.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor g).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : U.toGroupoids.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor (toGroupoids.map a ≫ g)).toFunctor.op.HasPointwiseRightKanExtension P]

/-- 2-cell transport `a⁻¹ g⁻¹ ≅ f⁻¹` along `φ : toGroupoids.map a ≫ g ≅ f`. -/
def etaleInverseImage_twoCell :
    etaleInverseImage g ⋙ etaleInverseImage (toGroupoids.map a) ≅ etaleInverseImage f :=
  (etaleInverseImage_compIso (toGroupoids.map a) g).symm ≪≫ etaleInverseImageIso φ

/-- The restricted unit `g⁻¹ F|_{V_étale} ⟶ a_small,* (f⁻¹ F|_{U_étale})` whose
adjunct is the comparison morphism `c_φ`. -/
def comparisonPushforward (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (restrictEtale V).obj ((etaleInverseImage g).obj F) ⟶
      (sheafPushforwardType a).obj
        ((restrictEtale U).obj ((etaleInverseImage f).obj F)) :=
  (restrictEtale V).map
      ((etaleMorphismOfTopoi (toGroupoids.map a)).adjunction.unit.app
          ((etaleInverseImage g).obj F) ≫
        (etaleDirectImage (toGroupoids.map a)).map
          ((etaleInverseImage_twoCell a f g φ).hom.app F)) ≫
    (AlgebraicSpace.compareBigSmall a ((etaleInverseImage f).obj F)).hom

/-- Inverse-image comparison `c_φ` of small étale sheaves associated to a
2-commutative triangle with algebraic-space legs. -/
def algebraicSpaceComparison (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (sheafPushforwardType a).leftAdjoint.obj
        ((restrictEtale V).obj ((etaleInverseImage g).obj F)) ⟶
      (restrictEtale U).obj ((etaleInverseImage f).obj F) :=
  ((Adjunction.ofIsRightAdjoint (sheafPushforwardType a)).homEquiv
      ((restrictEtale V).obj ((etaleInverseImage g).obj F))
      ((restrictEtale U).obj ((etaleInverseImage f).obj F))).symm
    (comparisonPushforward a f g φ F)

/-- `algebraicSpaceComparison` is the adjunct of `comparisonPushforward`. -/
theorem comparison_adjunct (F : Sheaf X.etaleTopology (Type (u + 1))) :
    algebraicSpaceComparison a f g φ F =
      ((Adjunction.ofIsRightAdjoint (sheafPushforwardType a)).homEquiv
          ((restrictEtale V).obj ((etaleInverseImage g).obj F))
          ((restrictEtale U).obj ((etaleInverseImage f).obj F))).symm
        (comparisonPushforward a f g φ F) :=
  sorry

/-- The sheaf morphism corresponding to `algebraicSpaceComparison` under the
small étale adjunction is `comparisonPushforward`. -/
theorem comparisonPushforward_spec (F : Sheaf X.etaleTopology (Type (u + 1))) :
    ((Adjunction.ofIsRightAdjoint (sheafPushforwardType a)).homEquiv
          ((restrictEtale V).obj ((etaleInverseImage g).obj F))
          ((restrictEtale U).obj ((etaleInverseImage f).obj F)))
        (algebraicSpaceComparison a f g φ F) =
      comparisonPushforward a f g φ F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
