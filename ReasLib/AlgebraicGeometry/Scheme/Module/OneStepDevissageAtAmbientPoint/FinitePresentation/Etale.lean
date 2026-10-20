/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation

/-!
# Finite presentation after an elementary étale refinement

This file compares finite presentation before and after a pointed elementary
étale refinement carrying an ambient-point one-step dévissage.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
  (F : X.Modules) [h_quasicoherent : F.IsQuasicoherent]
  [h_finiteType : F.IsFiniteType] (x : X)
  (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x)
  [h_refined_finiteType : LocallyOfFiniteType (Over.mk square.map).hom]
  (D : @OneStepDevissageAtAmbientPoint _ (Over.mk square.map)
    ((Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F)
    h_refined_finiteType
    (@pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent)
    (@pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType)
    square.source.obj.point)

/-- The finite map in the refined one-step dévissage is of finite presentation when
the original morphism is locally of finite presentation. -/
theorem piFinitePresentation_afterElementaryEtale
    [LocallyOfFinitePresentation f] :
    let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
    let h_quasicoherent' : F'.IsQuasicoherent :=
      @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
    let h_finiteType' : F'.IsFiniteType :=
      @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
    let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk square.map)
      F' h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let π := @OneStepDevissage.π _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E
    Scheme.Hom.FinitePresentation π.left := sorry

/-- After a pointed elementary étale refinement, finite presentation near the original
point, the distinguished auxiliary point, and its finite-map image are equivalent. -/
theorem finitePresentationAt_tfae_afterElementaryEtale
    [LocallyOfFinitePresentation f] :
    let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
    let h_quasicoherent' : F'.IsQuasicoherent :=
      @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
    let h_finiteType' : F'.IsFiniteType :=
      @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
    let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk square.map)
      F' h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let z := @OneStepDevissageAtAmbientPoint.z _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let y := @OneStepDevissageAtAmbientPoint.y _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let G := @OneStepDevissage.G _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E
    let π := @OneStepDevissage.π _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E
    List.TFAE
      [ IsFinitePresentationAt F x
      , IsFinitePresentationAt G z
      , IsFinitePresentationAt ((Scheme.Modules.pushforward π.left).obj G) y
      ] := sorry

/-- After a pointed elementary étale refinement, finite presentation of the original
stalk and the two distinguished refined stalks over their local rings is equivalent. -/
theorem stalkFinitePresentation_tfae_afterElementaryEtale
    [LocallyOfFinitePresentation f] :
    let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
    let h_quasicoherent' : F'.IsQuasicoherent :=
      @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
    let h_finiteType' : F'.IsFiniteType :=
      @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
    let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk square.map)
      F' h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let z := @OneStepDevissageAtAmbientPoint.z _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let y := @OneStepDevissageAtAmbientPoint.y _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType' square.source.obj.point D
    let Z := (@OneStepDevissage.Z _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E).left
    let Y := (@OneStepDevissage.Y _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E).left
    let G := @OneStepDevissage.G _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E
    let π := @OneStepDevissage.π _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType' ((Over.mk square.map).hom square.source.obj.point) E
    List.TFAE
      [ Module.FinitePresentation (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat F x)
      , Module.FinitePresentation (Z.presheaf.stalk z)
          (RingedSpace.stalkModuleCat G z)
      , Module.FinitePresentation (Y.presheaf.stalk y)
          (RingedSpace.stalkModuleCat
            ((Scheme.Modules.pushforward π.left).obj G) y)
      ] := sorry

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
