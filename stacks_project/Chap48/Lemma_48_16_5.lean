/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.ProjectionFormula
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Compactification.Of

/- Lemma 48.16.5 (1): the canonical maps
`Lf^*K ⊗ᴸ f⁺!𝒪_Y ⟶ f⁺!K` are functorial in bounded-below `K`. -/
@[stacks 0B6T] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.tensorNatTransPlus :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)],
    DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
        (DerivedQCoh.pullback f.hom.left ⋙
          DerivedQCoh.tensorRight (UpperShriek.dualizingObject f P A)) ⟶
      upperShriek f P A.plus ⋙
        DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace))

/- Lemma 48.16.5 (2): for composable `f` and `g`, the canonical upper-shriek
projection-formula maps form the stated commutative square for every bounded-below `K`. -/
@[stacks 0B6T] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice.tensorCommSq :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [TensorDescends (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends (Over.mk g.hom.left).left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [IsLocalization (Over.mk g.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Z.obj.left.toRingedSpace]
    [TensorDescends Z.obj.left.toRingedSpace]
    [IsLocalization Z.obj.left.toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_f).toRingedSpace]
    [TensorDescends (ambient C.P_f).toRingedSpace]
    [IsLocalization (ambient C.P_f).toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_g).toRingedSpace]
    [TensorDescends (ambient C.P_g).toRingedSpace]
    [IsLocalization (ambient C.P_g).toRingedSpace]
    [HomotopyTensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [TensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [IsLocalization (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_f).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_g).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom
      (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    [fAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_f).toShHom)]
    [fInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_f).toShHom)]
    [gAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_g).toShHom)]
    [gInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk g.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk g.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_g).toShHom)]
    [fgAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.modulePullbackDerived
        (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fgInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk (f ≫ g).hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk (f ≫ g).hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι (comp f g C.P_g C.P_bar)).toShHom)]
    (K : DerivedQCoh.Plus Z.obj.left),
    CommSq (UpperShriekCompChoice.tensorTop f g C K)
      (UpperShriekCompChoice.tensorSourceIso f g C K).hom
      ((UpperShriekCompChoice.ambientCompIso f g C).inv.app K)
      (UpperShriekCompChoice.tensorBottom f g C K))
