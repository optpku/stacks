/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Finiteness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Sheafy trace for proper morphisms of Noetherian algebraic spaces

For a proper morphism of Noetherian algebraic spaces, the canonical sheafy-trace
morphism `Rf_* RHom(L, a(K)) ⟶ RHom(Rf_* L, K)` is an isomorphism when `L` is
bounded above with coherent cohomology and `K` is bounded below.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a proper morphism of Noetherian algebraic spaces, the canonical sheafy-trace
morphism is an isomorphism when `L` is bounded above with coherent cohomology and
`K` is bounded below. -/
theorem sheafyTrace_isIso_of_proper {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [Proper f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    (hL_minus : (t.minus : ObjectProperty (ModuleDerived X)) L.obj)
    (hL_coh : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L.obj)
    (hK : K.obj.IsBoundedBelow) :
    IsIso (sheafyTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
