/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Topos
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SpacePushforward

/-!
# Inverse-image comparison for algebraic-space legs

A 2-commutative triangle of categories fibred in groupoids with algebraic-space
legs induces a comparison of small étale inverse images. It is the adjunct of
the restricted unit, transported along the 2-cell and the big/small pushforward
identification.
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

/-- The chosen right extension and the explicit pointwise extension represent
the same direct image, by their actual universal maps in both directions. -/
def algebraicSpaceDirectImageIso (H : Sheaf U.toGroupoids.etaleTopology (Type (u + 1))) :
    (etaleDirectImage (toGroupoids.map a)).obj H ≅ (etalePushforward a).obj H :=
  let kanEvidence : (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.HasPointwiseRightKanExtension H.obj :=
    fun _ ↦ inferInstance
  ObjectProperty.isoMk _
    (@rightKanExtensionUnique _ _ _ _ _ _
      ((toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.ran.obj H.obj)
      (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op H.obj
      ((toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op.ranCounit.app H.obj)
      { nonempty_isUniversal := ⟨CategoryTheory.Limits.terminalIsTerminal⟩ }
      (@pointwiseRightKanExtension _ _ _ _ _ _
        (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op H.obj kanEvidence)
      (@pointwiseRightKanExtensionCounit _ _ _ _ _ _
        (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op H.obj kanEvidence)
      { nonempty_isUniversal :=
          ⟨@pointwiseRightKanExtensionIsUniversal _ _ _ _ _ _
        (toCartesianBasedFunctor (toGroupoids.map a)).toFunctor.op H.obj kanEvidence⟩ })

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
    (restrictEtale V).map (algebraicSpaceDirectImageIso a ((etaleInverseImage f).obj F)).hom ≫
    (AlgebraicSpace.compareBigSmall a ((etaleInverseImage f).obj F)).hom

/-- Inverse-image comparison `c_φ` of small étale sheaves associated to a
2-commutative triangle with algebraic-space legs. -/
def algebraicSpaceComparison (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (sheafTypeInverseImage a).obj
        ((restrictEtale V).obj ((etaleInverseImage g).obj F)) ⟶
      (restrictEtale U).obj ((etaleInverseImage f).obj F) :=
  ((sheafAdjunctionType a).homEquiv
      ((restrictEtale V).obj ((etaleInverseImage g).obj F))
      ((restrictEtale U).obj ((etaleInverseImage f).obj F))).symm
    (comparisonPushforward a f g φ F)

/-- `algebraicSpaceComparison` is the adjunct of `comparisonPushforward`. -/
theorem algebraicSpaceComparison_adjunct (F : Sheaf X.etaleTopology (Type (u + 1))) :
    algebraicSpaceComparison a f g φ F =
      ((sheafAdjunctionType a).homEquiv
          ((restrictEtale V).obj ((etaleInverseImage g).obj F))
          ((restrictEtale U).obj ((etaleInverseImage f).obj F))).symm
        (comparisonPushforward a f g φ F) :=
  sorry

/-- The sheaf morphism corresponding to `algebraicSpaceComparison` under the
small étale adjunction is `comparisonPushforward`. -/
theorem comparisonPushforward_spec (F : Sheaf X.etaleTopology (Type (u + 1))) :
    ((sheafAdjunctionType a).homEquiv
          ((restrictEtale V).obj ((etaleInverseImage g).obj F))
          ((restrictEtale U).obj ((etaleInverseImage f).obj F)))
        (algebraicSpaceComparison a f g φ F) =
      comparisonPushforward a f g φ F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
