/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Localization

/-!
# Remark 96.10.2

If `f : X ⟶ Y` is a 1-morphism of categories fibred in groupoids over
`(Sch/S)_fppf`, `X` and `Y` are represented by algebraic spaces `F` and `G`,
and the induced morphism `F ⟶ G` is étale, then the two stacked squares of
ringed topoi with horizontal edges `f_small`, `f`, `f_small` and vertical edges
`i_F`, `π_F` on the left and `i_G`, `π_G` on the right commute.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}}
variable {X Y : GroupoidsOver S} (f : X ⟶ Y)
variable {F G : AlgebraicSpace S} (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y)
variable [AlgebraicSpace.Etale (moduleComparisonSpaceMorphism f eX eY)]
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
/- Remark 96.10.2: both squares formed by the canonical inclusion and restriction
morphisms commute with the morphisms of étale ringed topoi. -/
@[stacks 0GQA]
#check (AlgebraicGeometry.GroupoidsOver.etaleLocalization_commutes eX eY f :
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
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)))))
