/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.TraceComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.DerivedQCoh
open DerivedCategory.Plus
open CohomologyIn
open SheafOfModules.RingedSite
open RingedSpace.Hom

universe u

/- Remark 48.11.5: for a finite morphism `f : Y ⟶ X` of Noetherian schemes and
`K ∈ D⁺_QCoh(𝒪_X)`, the identification of `Rf_* a(K)` with
`RHom_{𝒪_X}(f_* 𝒪_Y, K)` makes the canonical trace commute with the map
induced by `𝒪_X ⟶ f_* 𝒪_Y`. -/
@[stacks 0AX3] #check (AlgebraicGeometry.Scheme.DerivedQCoh.finiteTrace_commutes :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
      (f : Y ⟶ X) [AlgebraicGeometry.IsFinite f]
      (K : AlgebraicGeometry.Scheme.DerivedQCoh.Plus X),
      ∃ (e :
        ((DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).obj
            ((AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj
              ((AlgebraicGeometry.Scheme.DerivedQCoh.finiteRightAdjoint f).obj
                ((toUnbounded
                    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))) ≅
          (DerivedCoextension.restriction
              (commRingSheafPushforwardMap f.toShHom)).obj
            ((DerivedCoextension.functor
                (commRingSheafPushforwardMap f.toShHom)).obj
              ((ambient
                (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))),
        e.hom ≫ AlgebraicGeometry.Scheme.DerivedQCoh.structureSheafInducedMap f K =
          ((DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).map
                (AlgebraicGeometry.Scheme.DerivedQCoh.finiteTraceMap f K) ≫
            (toUnbounded.compιIso
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).hom.app K)
