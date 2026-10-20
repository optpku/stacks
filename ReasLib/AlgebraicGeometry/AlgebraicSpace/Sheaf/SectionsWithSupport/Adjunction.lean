/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact

/-! # The direct-image adjunction for sections with support on a closed subspace -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The support-kernel inclusion is invertible on direct images from the closed subspace. -/
instance directImage_sectionsWithSupportOnι_isIso :
    IsIso (Functor.whiskerLeft (sheafPushforward AddCommGrpCat.{u + 1} i) (sectionsWithSupportOnι i)) := sorry

/-- The supported subsheaf is isomorphic to the direct image of its inverse image,
using the inverse-image/direct-image unit. -/
def sectionsWithSupportOnUnitIso :
    sectionsWithSupportOn i ≅ sectionsWithSupport i ⋙ sheafPushforward AddCommGrpCat.{u + 1} i :=
  (Functor.rightUnitor (sectionsWithSupportOn i)).symm ≪≫
    @asIso _ _ _ _
      (Functor.whiskerLeft (sectionsWithSupportOn i) (sheafAdjunction AddCommGrpCat.{u + 1} i).unit)
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _
        (Functor.whiskerLeft (sectionsWithSupportOn i) (sheafAdjunction AddCommGrpCat.{u + 1} i).unit)
        (fun F ↦ sectionsWithSupportOn_unit_isIso i F)) ≪≫
    (Functor.associator _ _ _).symm

/-- The unit for direct image and sections with support, obtained by inverting
the inverse-image counit and the support inclusion on direct images. -/
def sectionsWithSupportAdjunctionUnit :
    𝟭 (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) ⟶
      sheafPushforward AddCommGrpCat.{u + 1} i ⋙ sectionsWithSupport i :=
  (asIso (sheafAdjunction AddCommGrpCat.{u + 1} i).counit).inv ≫
    Functor.whiskerRight
      ((Functor.rightUnitor (sheafPushforward AddCommGrpCat.{u + 1} i)).inv ≫
        inv (Functor.whiskerLeft (sheafPushforward AddCommGrpCat.{u + 1} i) (sectionsWithSupportOnι i)))
      (sheafInverseImage AddCommGrpCat.{u + 1} i) ≫
    (Functor.associator _ _ _).hom

/-- The counit for direct image and sections with support is the inverse supported
unit followed by the supported-subsheaf inclusion. -/
def sectionsWithSupportAdjunctionCounit :
    sectionsWithSupport i ⋙ sheafPushforward AddCommGrpCat.{u + 1} i ⟶
      𝟭 (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  (sectionsWithSupportOnUnitIso i).inv ≫ sectionsWithSupportOnι i

/-- The support-adjunction unit and counit satisfy the left triangle identity. -/
theorem sectionsWithSupportAdjunction_left_triangle :
    Functor.whiskerRight (sectionsWithSupportAdjunctionUnit i) (sheafPushforward AddCommGrpCat.{u + 1} i) ≫
      (Functor.associator (sheafPushforward AddCommGrpCat.{u + 1} i) (sectionsWithSupport i)
        (sheafPushforward AddCommGrpCat.{u + 1} i)).hom ≫
      Functor.whiskerLeft (sheafPushforward AddCommGrpCat.{u + 1} i) (sectionsWithSupportAdjunctionCounit i) =
    𝟙 (𝟭 (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) ⋙ sheafPushforward AddCommGrpCat.{u + 1} i) := sorry

/-- The support-adjunction unit and counit satisfy the right triangle identity. -/
theorem sectionsWithSupportAdjunction_right_triangle :
    Functor.whiskerLeft (sectionsWithSupport i) (sectionsWithSupportAdjunctionUnit i) ≫
      (Functor.associator (sectionsWithSupport i) (sheafPushforward AddCommGrpCat.{u + 1} i)
        (sectionsWithSupport i)).inv ≫
      Functor.whiskerRight (sectionsWithSupportAdjunctionCounit i) (sectionsWithSupport i) =
    𝟙 (sectionsWithSupport i ⋙ 𝟭 (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})) := sorry

/-- Direct image along a closed immersion is left adjoint to sections with support. -/
def sectionsWithSupportAdjunction :
    sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport i :=
  Adjunction.mkOfUnitCounit {
    unit := sectionsWithSupportAdjunctionUnit i
    counit := sectionsWithSupportAdjunctionCounit i
    left_triangle := sectionsWithSupportAdjunction_left_triangle i
    right_triangle := sectionsWithSupportAdjunction_right_triangle i }

/-- Sections with support on a closed subspace are additive. -/
instance sectionsWithSupport_additive
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} i).Additive] :
    (sectionsWithSupport i).Additive :=
  (sectionsWithSupportAdjunction i).right_adjoint_additive

end AlgebraicGeometry.AlgebraicSpace
