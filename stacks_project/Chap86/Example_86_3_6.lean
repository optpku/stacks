/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

universe u

/- Example 86.3.6: for a proper morphism `f : X ⟶ Y` of Noetherian algebraic spaces
over a scheme `S`, `L ∈ D⁻_Coh(X)`, and `K ∈ D⁺_QCoh(𝒪_Y)`, the sheafy-trace map
from `Rf_* RHom(L, a(K))` to `RHom(Rf_* L, K)` is an isomorphism. -/
@[stacks 0GG5] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.sheafyTrace_isIso_of_proper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsNoetherian X] [IsNoetherian Y] [Proper f]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [ModuleDerived.HasDerivedAdjunction f]
      [Functor.Monoidal (ModuleDerived.pullback f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      (t.minus : ObjectProperty (ModuleDerived X)) L.obj →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (structureSheaf X)) L.obj →
          K.obj.IsBoundedBelow → IsIso (sheafyTraceMap f a adj L K))
