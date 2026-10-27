/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.AffineRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafificationCoefficients
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The topology on polynomial affine presentations inherited from the small étale site. -/
abbrev topology : GrothendieckTopology (category Λ X) :=
  (forget Λ X).inheritedTopology (smallEtaleTopology X)

/-- The cotangent topology is the inherited topology of the projection to étale charts. -/
theorem topology_eq : topology Λ X = (forget Λ X).inheritedTopology (smallEtaleTopology X) := rfl

/-- Commutative rings in the successor universe admit sheafification on the cotangent site. -/
instance topology_hasSheafify : HasSheafify (topology Λ X) CommRingCat.{u + 1} := by
  exact PullbackFactory.CoefficientSheafification.commRing (topology Λ X)

/-- The universe-lifted presheaf of global functions on polynomial affine targets.
Its values are prescribed before sheafification; they need not satisfy the sheaf condition. -/
def structurePresheaf : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (affineScheme Λ X).op ⋙ Scheme.Γ ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The universe-lifted structure presheaf pulled back from étale charts of the algebraic space. -/
def underlinePresheaf : (category Λ X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (forget Λ X).op ⋙ commStructurePresheaf X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The affine-target presheaf with coefficients lifted to the successor universe. -/
abbrev structurePresheafLift := structurePresheaf Λ X
/-- The pulled-back structure presheaf with coefficients in the successor universe. -/
abbrev underlinePresheafLift := underlinePresheaf Λ X


/-- The sheafification of the presheaf of global functions on polynomial affine targets.
The displayed affine global sections describe the presheaf, rather than the values of this sheaf. -/
noncomputable def structureSheaf : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).obj (structurePresheaf Λ X)

/-- The sheafification of the structure presheaf pulled back from the small étale site.
Comparison with the original presheaf is through the canonical sheafification unit. -/
noncomputable def underlineSheaf : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  (presheafToSheaf (topology Λ X) CommRingCat.{u + 1}).obj (underlinePresheaf Λ X)

/-- The continuous pullback of the lifted étale structure sheaf to polynomial affine
presentations, whose underlying presheaf is the pulled-back structure presheaf. -/
def underlinePullbackSheaf : Sheaf (topology Λ X) CommRingCat.{u + 1} :=
  ((forget Λ X).sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology Λ X) (smallEtaleTopology X)).obj (commStructureSheafLift X)

/-- The canonical isomorphism from the sheafified pulled-back structure presheaf to the
continuous pullback of the lifted étale structure sheaf. -/
noncomputable def underlineSheafIso :
    underlineSheaf Λ X ≅ underlinePullbackSheaf Λ X :=
  (CategoryTheory.sheafificationIso (underlinePullbackSheaf Λ X)).symm

/-- The sheafified affine-target structure sheaf with successor-universe coefficients. -/
abbrev structureSheafLift := structureSheaf Λ X
/-- The sheafified pulled-back structure sheaf with successor-universe coefficients. -/
abbrev underlineSheafLift := underlineSheaf Λ X

/-- The canonical map from affine-target global functions to their associated sheaf. -/
noncomputable def structureSheafUnit : structurePresheaf Λ X ⟶ (structureSheaf Λ X).obj :=
  toSheafify (topology Λ X) (structurePresheaf Λ X)

/-- The canonical map from the pulled-back structure presheaf to its associated sheaf. -/
noncomputable def underlineSheafUnit : underlinePresheaf Λ X ⟶ (underlineSheaf Λ X).obj :=
  toSheafify (topology Λ X) (underlinePresheaf Λ X)

end AlgebraicGeometry.AlgebraicSpace.Cotangent
