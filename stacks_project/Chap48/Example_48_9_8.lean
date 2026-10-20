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
open DerivedCategory.Plus
open CohomologyIn
open SheafOfModules.RingedSite
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Example 48.9.8: for a closed immersion `i : Z ⟶ X` of Noetherian schemes and
`K ∈ D⁺_QCoh(𝒪_X)`, the identification of `i_* a(K)` with
`RHom_{𝒪_X}(i_* 𝒪_Z, K)` intertwines the trace with the map induced by
`𝒪_X ⟶ i_* 𝒪_Z`. -/
@[stacks 0B6M]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionTrace_commutes :
    ∀ {X Z : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Z] (i : Z ⟶ X) [IsClosedImmersion i] (K : Plus X),
      ∃ (e :
        ((DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).obj
            ((pushforwardCohomologyIn i).obj
              ((finiteRightAdjoint i).obj
                ((toUnbounded
                    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))) ≅
          (DerivedCoextension.restriction
              (commRingSheafPushforwardMap i.toShHom)).obj
            ((DerivedCoextension.functor
                (commRingSheafPushforwardMap i.toShHom)).obj
              ((ambient
                (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).obj K))),
        e.hom ≫ structureSheafInducedMap i K =
          ((DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι).map
                (finiteTraceMap i K) ≫
            (toUnbounded.compιIso
              (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).hom.app K)

end AlgebraicGeometry.Scheme.DerivedQCoh
