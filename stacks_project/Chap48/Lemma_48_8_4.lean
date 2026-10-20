/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.8.4 -/
@[stacks 0B6R] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMap_comp :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      [CompactSpace Z] [QuasiSeparatedSpace Z]
      [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [HomotopyTensorDescends Z.toRingedSpace] [TensorDescends Z.toRingedSpace]
      [IsLocalization Z.toRingedSpace]
      [HasPair (opensRingedSiteHom f.toShHom)]
      [HasPair (opensRingedSiteHom g.toShHom)]
      [HasPair (opensRingedSiteHom (f ≫ g).toShHom)]
      [Functor.Monoidal (modulePullbackDerived f.toShHom)]
      [Functor.Monoidal (modulePullbackDerived g.toShHom)]
      [Functor.Monoidal (modulePullbackDerived (f ≫ g).toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (b : DerivedQCoh Z ⥤ DerivedQCoh Y)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (bAdjunction : pushforwardCohomologyIn g ⊣ b)
      (K : DerivedQCoh Z),
      (pullbackTensorCompIso f g
          (RingedSpace.modulePullbackDerived.compComparison_isIso f.toShHom g.toShHom)
          K (b.obj (structureSheaf Z)) (a.obj (structureSheaf Y))).hom ≫
          tensorObjAssocMapRight ((pullback (f ≫ g)).obj K)
            ((pullback f).obj (b.obj (structureSheaf Z))) (a.obj (structureSheaf Y))
            (a.obj (b.obj (structureSheaf Z)))
            (pullbackTensorDualityMap f a aAdjunction (b.obj (structureSheaf Z))) ≫
          pullbackTensorDualityMap (f ≫ g) (b ⋙ a)
            (compositeRightAdjunction f g
              (RingedSpace.modulePullbackDerived.compComparison_isIso
                f.toShHom g.toShHom)
              a b aAdjunction bAdjunction) K =
        pullbackTensorDualityMap f a aAdjunction
            (tensorObj ((pullback g).obj K) (b.obj (structureSheaf Z))) ≫
          a.map (pullbackTensorDualityMap g b bAdjunction K))

end AlgebraicGeometry.Scheme.DerivedQCoh
