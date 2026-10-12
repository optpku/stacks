/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

/-- For an open immersion, the extension-by-zero/restriction adjunction unit
at every abelian étale sheaf is an isomorphism. -/
instance abelianExtensionByZero_unit_isIso_of_isOpenImmersion
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((abelianExtensionByZero_adjunction j).unit.app F) := sorry

/-- For an open immersion, the pullback/direct-image adjunction counit
at every abelian étale sheaf is an isomorphism. -/
instance abelianDirectImage_counit_isIso_of_isOpenImmersion
    (j : U ⟶ X) [IsOpenImmersion j]
    [((smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso (((smallEtalePullback j).sheafAdjunctionContinuous
      AddCommGrpCat.{u} X.smallEtaleTopology U.smallEtaleTopology).counit.app F) := sorry

/-- An abelian étale sheaf restricting to `F` along an open immersion and
having zero geometric stalks outside the open is isomorphic to the extension
by zero of `F`. -/
theorem abelianExtensionByZero_unique_of_restriction_and_vanishingStalks
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F)
    (hG : ∀ xbar : GeometricPoint X, xbar.image ∉ j.opensRange →
      IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G)) :
    Nonempty (G ≅ (abelianExtensionByZero j).obj F) := sorry

/-- Extension by zero along an open immersion has zero stalk at every
geometric point outside the image of the immersion. -/
theorem abelianExtensionByZero_stalk_isZero_of_not_mem_opensRange
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (xbar : GeometricPoint X) (hx : xbar.image ∉ j.opensRange) :
    IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
      ((abelianExtensionByZero j).obj F)) := sorry

end AlgebraicGeometry.Scheme
