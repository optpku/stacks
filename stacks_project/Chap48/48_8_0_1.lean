/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.«48_8_0_1_Comparison»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open AlgebraicGeometry.Scheme.DerivedQCoh

noncomputable section

universe u

/- 48.8.0.1: for a morphism `f : X ⟶ Y`, a right adjoint `a` to `Rf_*`, and
`K : DerivedQCoh Y`, the projection formula and the counit define the canonical map
`Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)`. -/
@[stacks 0A9S] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMap :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [HomotopyTensorDescends X.toRingedSpace]
      [TensorDescends X.toRingedSpace]
      [IsLocalization X.toRingedSpace]
      [HomotopyTensorDescends Y.toRingedSpace]
      [TensorDescends Y.toRingedSpace]
      [IsLocalization Y.toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K : Scheme.DerivedQCoh Y),
      tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y)) ⟶ a.obj K)
