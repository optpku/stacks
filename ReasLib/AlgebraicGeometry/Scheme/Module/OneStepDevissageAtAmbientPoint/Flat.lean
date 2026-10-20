module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Flatness in one-step dévissages after elementary étale refinement
-/

@[expose] public section

open CategoryTheory Filter
open scoped AlgebraicGeometry Topology

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

/-- Flatness over the base near the original point, near the distinguished auxiliary
point, and near its image on the smooth model are equivalent. -/
theorem eventually_flatOverAt_tfae_afterElementaryEtale :
    let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
    let h_quasicoherent' : F'.IsQuasicoherent :=
      @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
    let h_finiteType' : F'.IsFiniteType :=
      @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
    let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk square.map)
      F' h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let z := @OneStepDevissageAtAmbientPoint.z _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let y := @OneStepDevissageAtAmbientPoint.y _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let Z := @OneStepDevissage.Z _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let Y := @OneStepDevissage.Y _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let G := @OneStepDevissage.G _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let π := @OneStepDevissage.π _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    List.TFAE
      [ ∀ᶠ x' in 𝓝 x, flatOverAt F f x'
      , ∀ᶠ z' in 𝓝 z, flatOverAt G Z.hom z'
      , ∀ᶠ y' in 𝓝 y,
          flatOverAt ((Scheme.Modules.pushforward π.left).obj G) Y.hom y'
      ] := sorry

/-- Flatness at the original point, the distinguished auxiliary point, and its image
on the smooth model are equivalent. -/
theorem flatOverAt_tfae_afterElementaryEtale :
    let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
    let h_quasicoherent' : F'.IsQuasicoherent :=
      @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
    let h_finiteType' : F'.IsFiniteType :=
      @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
    let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk square.map)
      F' h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let z := @OneStepDevissageAtAmbientPoint.z _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let y := @OneStepDevissageAtAmbientPoint.y _ (Over.mk square.map) F'
      h_refined_finiteType h_quasicoherent' h_finiteType'
      square.source.obj.point D
    let Z := @OneStepDevissage.Z _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let Y := @OneStepDevissage.Y _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let G := @OneStepDevissage.G _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    let π := @OneStepDevissage.π _ (Over.mk square.map) F' h_refined_finiteType
      h_quasicoherent' h_finiteType'
      ((Over.mk square.map).hom square.source.obj.point) E
    List.TFAE
      [ flatOverAt F f x
      , flatOverAt G Z.hom z
      , flatOverAt ((Scheme.Modules.pushforward π.left).obj G) Y.hom y
      ] := sorry

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
