/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.AffineRealization
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Fibered
public import ReasLib.AlgebraicGeometry.Scheme.Sites.FunctionSheaves
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

/-!
# Associated structure sheaves of polynomial affine diagrams

Global functions on the target and on the open vertex specify presheaves.
Their associated sheaves are formed after lifting coefficients to the successor
universe. In particular, raw target functions are not asserted to satisfy the
sheaf condition for empty coverings. The topology includes all inherited
Zariski coverings. A common construction for schemes and algebraic spaces over
a base site is a natural further generalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- The topology on polynomial affine diagrams inherited from the small Zariski site. -/
abbrev topology : GrothendieckTopology (category Λ X) :=
  (forgetZariski Λ X).inheritedTopology X.smallZariskiTopology

/-- The raw presheaf of global functions on the affine target. -/
def structurePresheafComm : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  Scheme.Site.commStructurePresheaf (affineRealization Λ X)

/-- Raw affine-target functions evaluate to the global sections of the target scheme. -/
theorem structurePresheafComm_obj (P : category Λ X) :
    (structurePresheafComm Λ X).obj (op P) = Γ(P.right.obj.left, ⊤) := rfl

/-- The raw presheaf of functions on the open vertex. -/
def inverseImageStructurePresheafComm : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (forgetZariski Λ X).op ⋙
    Scheme.Site.commStructurePresheaf (SmallStandardTopology.toScheme .zariski X)

/-- Raw open-vertex functions evaluate to the global sections of the open subscheme. -/
theorem inverseImageStructurePresheafComm_obj (P : category Λ X) :
    (inverseImageStructurePresheafComm Λ X).obj (op P) = Γ(P.left.left, ⊤) := rfl

/-- Affine-target global functions with coefficients in the successor universe. -/
def structurePresheafCommLift : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  structurePresheafComm Λ X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- Open-vertex global functions with coefficients in the successor universe. -/
def inverseImageStructurePresheafCommLift : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  inverseImageStructurePresheafComm Λ X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The associated sheaf of the lifted affine-target global-functions presheaf. -/
def structureSheafComm : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).obj
    (structurePresheafCommLift Λ X)

/-- The associated sheaf of the lifted open-vertex global-functions presheaf. -/
def inverseImageStructureSheafComm : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).obj
    (inverseImageStructurePresheafCommLift Λ X)

/-- The unit from lifted affine-target functions to their associated sheaf. -/
def structureSheafUnit :
    structurePresheafCommLift Λ X ⟶ (structureSheafComm Λ X).obj :=
  toSheafify (topology Λ X) (structurePresheafCommLift Λ X)

/-- The unit from lifted open-vertex functions to their associated sheaf. -/
def inverseImageStructureSheafUnit :
    inverseImageStructurePresheafCommLift Λ X ⟶ (inverseImageStructureSheafComm Λ X).obj :=
  toSheafify (topology Λ X) (inverseImageStructurePresheafCommLift Λ X)

/-- The canonical identification of associated open-vertex functions with the
continuous pullback of the lifted small Zariski structure sheaf. -/
def inverseImageStructureSheafCommIso :
    inverseImageStructureSheafComm Λ X ≅
      ((forgetZariski Λ X).sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology Λ X) X.smallZariskiTopology).obj
          (Scheme.AssociatedModule.smallCommStructureSheaf .zariski X) :=
  (sheafificationIso
    (((forgetZariski Λ X).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology Λ X) X.smallZariskiTopology).obj
        (Scheme.AssociatedModule.smallCommStructureSheaf .zariski X))).symm

end AlgebraicGeometry.Scheme.CotangentSite
