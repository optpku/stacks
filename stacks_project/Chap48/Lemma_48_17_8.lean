/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Duality
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Over
open RingedSite.Hom.DerivedAdjunction RingedSpace.ModuleDerived.KFlat

universe u

/- Lemma 48.17.8: for a finite-type separated morphism `f : X ⟶ Y`, a
dualizing complex `K`, and a bounded-below coherent complex `M`, the canonical
morphism `f⁺!M ⟶ Rℋom(Lf^*Rℋom(M, K), f⁺!K)` is invertible. -/
@[stacks 0AU2] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualityMap_isIso :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      (P : Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : Scheme.DerivedQCoh.PlusRightAdjoint
        (Scheme.Compactification.Of.ambientMorphism P))
      [HomotopyTensorDescends X.obj.left.toRingedSpace]
      [TensorDescends X.obj.left.toRingedSpace]
      [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
      [IsLocalization X.obj.left.toRingedSpace]
      [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
      [HomotopyTensorDescends Y.obj.left.toRingedSpace]
      [TensorDescends Y.obj.left.toRingedSpace]
      [IsLocalization Y.obj.left.toRingedSpace]
      [HomotopyTensorDescends (Scheme.Compactification.Of.ambient P).toRingedSpace]
      [TensorDescends (Scheme.Compactification.Of.ambient P).toRingedSpace]
      [IsLocalization (Scheme.Compactification.Of.ambient P).toRingedSpace]
      [HasPair (RingedSpace.opensRingedSiteHom
        (Scheme.Compactification.Of.ambientMorphism P).toShHom)]
      [ambientPullbackMonoidal : @Functor.Monoidal
        (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
        (RingedSpace.ModuleDerived
          (Scheme.Compactification.Of.ambient P).toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory
            (Scheme.Compactification.Of.ambient P).toRingedSpace)
        (RingedSpace.modulePullbackDerived
          (Scheme.Compactification.Of.ambientMorphism P).toShHom)]
      [interiorPullbackMonoidal : @Functor.Monoidal
        (RingedSpace.ModuleDerived
          (Scheme.Compactification.Of.ambient P).toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory
            (Scheme.Compactification.Of.ambient P).toRingedSpace)
        (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
          (RingedSpace.ModuleDerived.monoidalCategory
            (Over.mk f.hom.left).left.toRingedSpace)
        (RingedSpace.modulePullbackDerived
          (Scheme.Compactification.Of.ι P).toShHom)]
      (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace))
      (H_P : MonoidalClosed (RingedSpace.ModuleDerived
        (Scheme.Compactification.Of.ambient P).toRingedSpace))
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.obj.left.toRingedSpace))
      (K M : Scheme.DerivedQCoh.Plus Y.obj.left)
      (hK : Scheme.IsDualizingComplex K.obj.obj)
      (hM_coherent : DerivedCategory.Plus.cohomologyIn
        (SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf) M.obj),
      IsIso (Scheme.Compactification.Of.UpperShriek.dualityMap
        f P A H_Y H_P H_X K M hK hM_coherent))
