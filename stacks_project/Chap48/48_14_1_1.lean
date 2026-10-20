/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.«48_8_0_1»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- 48.14.1.1: for an effective Cartier divisor `i : D ⟶ X` and
`K : DerivedQCoh X`, the canonical morphism
`Li^*K ⊗ᴸ Rℋom(𝒪_D, 𝒪_X) ⟶ Rℋom(𝒪_D, K)` is represented using the canonical
derived pullback-tensor duality morphism. -/
@[stacks 0B4C] #check
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
