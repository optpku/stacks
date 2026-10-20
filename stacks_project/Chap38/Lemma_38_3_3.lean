/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap38.Lemma_38_3_2
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint.FinitePresentation.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.3.3 (1): after an elementary étale refinement, local finite presentation
of the original morphism implies finite presentation of the finite map in the resulting
ambient-point one-step dévissage. -/
@[stacks 057T] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.piFinitePresentation_afterElementaryEtale :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [h_quasicoherent : F.IsQuasicoherent]
      [h_finiteType : F.IsFiniteType] (x : X)
      (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x)
      [h_refined_finiteType : LocallyOfFiniteType (Over.mk square.map).hom]
      (D : @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint _
        (Over.mk square.map)
        ((Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F)
        h_refined_finiteType
        (@Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent)
        (@Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType)
        square.source.obj.point)
      [LocallyOfFinitePresentation f],
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      let h_quasicoherent' : F'.IsQuasicoherent :=
        @Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent
      let h_finiteType' : F'.IsFiniteType :=
        @Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType
      let E := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.toOneStepDevissage
        _ (Over.mk square.map) F' h_refined_finiteType
        h_quasicoherent' h_finiteType' square.source.obj.point D
      let π := @AlgebraicGeometry.Scheme.Modules.OneStepDevissage.π _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E
      Scheme.Hom.FinitePresentation π.left)

/- Lemma 38.3.3 (2): finite presentation near the original point, the distinguished
auxiliary point, and its image under the finite map are equivalent. -/
@[stacks 057T] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.finitePresentationAt_tfae_afterElementaryEtale :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [h_quasicoherent : F.IsQuasicoherent]
      [h_finiteType : F.IsFiniteType] (x : X)
      (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x)
      [h_refined_finiteType : LocallyOfFiniteType (Over.mk square.map).hom]
      (D : @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint _
        (Over.mk square.map)
        ((Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F)
        h_refined_finiteType
        (@Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent)
        (@Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType)
        square.source.obj.point)
      [LocallyOfFinitePresentation f],
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      let h_quasicoherent' : F'.IsQuasicoherent :=
        @Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent
      let h_finiteType' : F'.IsFiniteType :=
        @Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType
      let E := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.toOneStepDevissage
        _ (Over.mk square.map) F' h_refined_finiteType
        h_quasicoherent' h_finiteType' square.source.obj.point D
      let z := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.z _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        square.source.obj.point D
      let y := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.y _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        square.source.obj.point D
      let G := @AlgebraicGeometry.Scheme.Modules.OneStepDevissage.G _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E
      let π := @AlgebraicGeometry.Scheme.Modules.OneStepDevissage.π _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E
      List.TFAE
        [ Scheme.Modules.IsFinitePresentationAt F x
        , Scheme.Modules.IsFinitePresentationAt G z
        , Scheme.Modules.IsFinitePresentationAt ((Scheme.Modules.pushforward π.left).obj G) y
        ])

/- Lemma 38.3.3 (3): finite presentation of the original stalk and the two
distinguished refined stalks over their respective local rings is equivalent. -/
@[stacks 057T] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.stalkFinitePresentation_tfae_afterElementaryEtale :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [h_quasicoherent : F.IsQuasicoherent]
      [h_finiteType : F.IsFiniteType] (x : X)
      (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x)
      [h_refined_finiteType : LocallyOfFiniteType (Over.mk square.map).hom]
      (D : @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint _
        (Over.mk square.map)
        ((Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F)
        h_refined_finiteType
        (@Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent)
        (@Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType)
        square.source.obj.point)
      [LocallyOfFinitePresentation f],
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      let h_quasicoherent' : F'.IsQuasicoherent :=
        @Scheme.Modules.pullback_isQuasicoherent _ _
          square.source.obj.toEtale.hom F h_quasicoherent
      let h_finiteType' : F'.IsFiniteType :=
        @Scheme.Modules.pullback_isFiniteType _ _
          square.source.obj.toEtale.hom F h_finiteType
      let E := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.toOneStepDevissage
        _ (Over.mk square.map) F' h_refined_finiteType
        h_quasicoherent' h_finiteType' square.source.obj.point D
      let z := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.z _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        square.source.obj.point D
      let y := @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.y _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        square.source.obj.point D
      let Z := (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.Z _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E).left
      let Y := (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.Y _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E).left
      let G := @AlgebraicGeometry.Scheme.Modules.OneStepDevissage.G _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E
      let π := @AlgebraicGeometry.Scheme.Modules.OneStepDevissage.π _
        (Over.mk square.map) F' h_refined_finiteType h_quasicoherent' h_finiteType'
        ((Over.mk square.map).hom square.source.obj.point) E
      List.TFAE
        [ Module.FinitePresentation (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat F x)
        , Module.FinitePresentation (Z.presheaf.stalk z)
            (RingedSpace.stalkModuleCat G z)
        , Module.FinitePresentation (Y.presheaf.stalk y)
            (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward π.left).obj G) y)
        ])
