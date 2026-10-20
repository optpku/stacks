/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward.Coproduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 75.6.2: for a scheme `S` and a quasi-separated and quasi-compact morphism
`f : X ⟶ Y` of algebraic spaces over `S`, the restricted derived pushforward
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums. -/
@[stacks 08FB] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.preservesCoproducts :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] (I : Type u),
      PreservesColimitsOfShape (Discrete I) (pushforwardCohomologyIn f))
