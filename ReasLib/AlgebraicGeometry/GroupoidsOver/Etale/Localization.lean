/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.RepresentedSections
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Sheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]

set_option maxHeartbeats 800000 in
/-- For an étale morphism of algebraic spaces representing a morphism of categories
fibred in groupoids, both the inclusion and restriction morphisms of their small
étale ringed topoi commute with the induced morphisms of ringed topoi. -/
theorem etaleLocalization_commutes
    [AlgebraicSpace.Etale (moduleComparisonSpaceMorphism f eX eY)] :
    -- Local instance justification (noncanonical choice): this small-section witness is derived from the explicit representing equivalences eX and eY, which cannot be inferred from f; keep the presentation-dependent installation local.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u}
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))
        (inclusion G Y eY))
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (inclusion F X eX) (etaleRingedToposHom f))) ∧
    Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (etaleRingedToposHom f) (piToposHom G Y eY))
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (piToposHom F X eX)
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
