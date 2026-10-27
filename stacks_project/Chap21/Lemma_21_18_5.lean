/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.MixedTensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.18.5

The reusable owner factors pullback through modules over `f⁻¹𝒪_Y` and models the mixed derived
tensor product by derived extension of scalars followed by the canonical K-flat tensor product over
`𝒪_X`.  The chapter entry only recalls the canonical comparison and its isomorphism views.
-/

open CategoryTheory RingedSite.Hom
open CategoryTheory.MonoidalCategory

noncomputable section

universe uX vX uY vY w

variable {C : Type uX} [Category.{vX} C] {D : Type uY} [Category.{vY} D]
variable {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
  [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify JY AddCommGrpCat.{w}]
  [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [hX : UnivLE.{max uX vX, w}] [hY : UnivLE.{max uY vY, w}]
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(f.base.sheafPushforwardContinuous CommRingCat.{w} JY JX).IsRightAdjoint]
variable [((PullbackFactorization.inverseImage f).modulePushforward.{w}).IsRightAdjoint]
variable [((PullbackFactorization.scalarExtension f).modulePushforward.{w}).IsRightAdjoint]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{w} (PullbackFactorization.scalarExtension f))
    (ModuleQis.{w}
      (RingedSite.ofCommRingSheaf JX (inverseImageStructureSheaf f)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{w} (PullbackFactorization.inverseImage f))
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [Functor.HasLeftDerivedFunctor
    (compositePullbackToDerived.{w}
      (PullbackFactorization.scalarExtension f) (PullbackFactorization.inverseImage f))
    (ModuleQis.{w} (RingedSite.ofCommRingSheaf JY OY))]
variable [@ModuleDerived.KFlat.HomotopyTensorDescends C _ JX _ _ _ hX OX]
variable [@ModuleDerived.KFlat.TensorDescends C _ JX _ _ _ hX OX _]
variable [@ModuleDerived.KFlat.IsLocalization C _ JX _ _ _ hX OX]

#check (modulePullbackDerived.MixedTensor.compComparison_isIso (hX := hX) (hY := hY) f :
  IsIso (modulePullbackDerived.compComparison
    (PullbackFactorization.scalarExtension f) (PullbackFactorization.inverseImage f)))

variable [IsIso (modulePullbackDerived.compComparison
  (PullbackFactorization.scalarExtension f) (PullbackFactorization.inverseImage f))]

/- Lemma 21.18.5 (08I6): the canonical bifunctorial comparison identifies tensor with factorized
derived pullback and the mixed tensor over the inverse-image structure sheaf. -/
@[stacks 08I6 "canonical mixed derived tensor comparison"]
#check (RingedSite.Hom.modulePullbackDerived.MixedTensor.natIso (hX := hX) (hY := hY) f :
  modulePullbackDerived.MixedTensor.tensorAction
      (modulePullbackDerived.MixedTensor.pullback (hX := hX) (hY := hY) f) ≅
    modulePullbackDerived.MixedTensor.tensorAction
      (modulePullbackDerived.MixedTensor.inverseImage (hX := hX) (hY := hY) f ⋙
        modulePullbackDerived.MixedTensor.scalarExtension (hX := hX) f))

#check (modulePullbackDerived.MixedTensor.iso (hX := hX) (hY := hY) f :
  ∀ (F : @ModuleDerived.{w, uX, vX, w} (RingedSite.ofCommRingSheaf JX OX) hX)
    (G : @ModuleDerived.{w, uY, vY, w} (RingedSite.ofCommRingSheaf JY OY) hY),
    (modulePullbackDerived.MixedTensor.tensorAction
      (modulePullbackDerived.MixedTensor.pullback (hX := hX) (hY := hY) f)).obj (F, G) ≅
      modulePullbackDerived.MixedTensor.obj (hX := hX) f F
        ((modulePullbackDerived.MixedTensor.inverseImage (hX := hX) (hY := hY) f).obj G))

#check (PullbackFactorization.hom_eq f : PullbackFactorization.hom f = f)
