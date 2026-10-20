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

/-- The canonical comparison `j_! F ⟶ G` attached to an identification
`e : j⁻¹ G ≅ F`: the adjoint of `e.inv : F ⟶ j⁻¹ G` under the
extension-by-zero/restriction adjunction. -/
noncomputable def abelianExtensionByZeroComparison
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F) :
    (abelianExtensionByZero j).obj F ⟶ G :=
  ((abelianExtensionByZero_adjunction j).homEquiv F G).symm e.inv

/-- The comparison `j_! F ⟶ G` restricts, after the unit of the adjunction, to the
given identification `F ≅ j⁻¹ G`. -/
theorem abelianExtensionByZeroComparison_adjunction_unit
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F) :
    (abelianExtensionByZero_adjunction j).unit.app F ≫
        (etaleRestrictionSheaf j AddCommGrpCat.{u}).map
          (abelianExtensionByZeroComparison j F G e) =
      e.inv :=
  (((abelianExtensionByZero_adjunction j).homEquiv_unit F G
      (abelianExtensionByZeroComparison j F G e)).symm.trans
    (Equiv.apply_symm_apply _ e.inv))

/-- An abelian étale sheaf `G` with an identification `j⁻¹ G ≅ F` and with zero
geometric stalks outside the open makes the canonical comparison `j_! F ⟶ G`
an isomorphism. -/
theorem isIso_abelianExtensionByZeroComparison
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F)
    (hG : ∀ xbar : GeometricPoint X, xbar.image ∉ j.opensRange →
      IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G)) :
    IsIso (abelianExtensionByZeroComparison j F G e) := sorry

/-- Uniqueness of extension by zero: an abelian étale sheaf restricting to `F`
along an open immersion and having zero geometric stalks outside the open is
identified with `j_! F` by the inverse of the canonical comparison. -/
noncomputable def abelianExtensionByZeroIsoOfRestriction
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F)
    (hG : ∀ xbar : GeometricPoint X, xbar.image ∉ j.opensRange →
      IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G)) :
    G ≅ (abelianExtensionByZero j).obj F :=
  haveI := isIso_abelianExtensionByZeroComparison j F G e hG
  (asIso (abelianExtensionByZeroComparison j F G e)).symm

/-- The inverse of the uniqueness isomorphism is the canonical comparison. -/
@[simp]
theorem abelianExtensionByZeroIsoOfRestriction_inv
    (j : U ⟶ X) [IsOpenImmersion j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅ F)
    (hG : ∀ xbar : GeometricPoint X, xbar.image ∉ j.opensRange →
      IsZero ((GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G)) :
    (abelianExtensionByZeroIsoOfRestriction j F G e hG).inv =
      abelianExtensionByZeroComparison j F G e :=
  rfl

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
