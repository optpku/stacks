/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InverseImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallSectionsOfRightKan
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DerivedComparison

/-!
# Small-coefficient abelian étale inverse image
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Inverse image of abelian étale sheaves along a 1-morphism of categories
fibred in groupoids, as continuous sheaf pushforward of the cartesian total
functor at coefficient universe `u`. -/
abbrev etaleAbelianInverseImage {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    Sheaf Y.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.etaleTopology AddCommGrpCat.{u} :=
  (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous
    AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology

/-- `etaleAbelianInverseImage h` is continuous sheaf pushforward of abelian groups
along the cartesian total functor. -/
theorem etaleAbelianInverseImage_eq {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    etaleAbelianInverseImage h =
      (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology :=
  rfl

/-- Inverse image of abelian étale sheaves is additive. -/
instance etaleAbelianInverseImage.instAdditive {X Y : GroupoidsOver S}
    (h : X ⟶ Y) : (etaleAbelianInverseImage h).Additive :=
  inferInstance

/-- Inverse image of abelian étale sheaves preserves homology. -/
instance etaleAbelianInverseImage.instPreservesHomology {X Y : GroupoidsOver S}
    (h : X ⟶ Y) : (etaleAbelianInverseImage h).PreservesHomology :=
  sorry

/-- Inverse image of abelian étale sheaves preserves finite limits. -/
instance etaleAbelianInverseImage.instPreservesFiniteLimits
    {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    PreservesFiniteLimits (etaleAbelianInverseImage h) :=
  sorry

/-- Inverse image of abelian étale sheaves preserves finite colimits. -/
instance etaleAbelianInverseImage.instPreservesFiniteColimits
    {X Y : GroupoidsOver S} (h : X ⟶ Y) :
    PreservesFiniteColimits (etaleAbelianInverseImage h) :=
  sorry

/-- Continuous-cocontinuous adjunction `h⁻¹ ⊣ h_*` on abelian étale sheaves. -/
abbrev etaleAbelianInverseImage_adjunction {X Y : GroupoidsOver S} (h : X ⟶ Y)
    [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleAbelianInverseImage h ⊣ etaleAbelianPushforward h :=
  (toCartesianBasedFunctor h).toFunctor.sheafAdjunctionCocontinuous
    AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology

/-- Inverse image along a composite 1-morphism identifies with the composite of
étale abelian inverse images. -/
def etaleAbelianInverseImage_compIso {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleAbelianInverseImage (h ≫ k) ≅
      etaleAbelianInverseImage k ⋙ etaleAbelianInverseImage h :=
  (sheafPushforwardContinuousComp'
      (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)
      AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology Z.etaleTopology).symm

/-- `etaleAbelianInverseImage_compIso` is the continuous-pushforward comparison along
total-functor composition. -/
theorem etaleAbelianInverseImage_compIso_eq {X Y Z : GroupoidsOver S}
    (h : X ⟶ Y) (k : Y ⟶ Z) :
    etaleAbelianInverseImage_compIso h k =
      (sheafPushforwardContinuousComp'
          (ObjectProperty.FullSubbicategory.toFunctor.compIso h k)
          AddCommGrpCat.{u} X.etaleTopology Y.etaleTopology
          Z.etaleTopology).symm :=
  rfl


end AlgebraicGeometry.GroupoidsOver
