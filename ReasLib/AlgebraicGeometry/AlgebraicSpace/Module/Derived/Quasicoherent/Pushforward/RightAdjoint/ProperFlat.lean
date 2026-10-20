/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Invertibility of the duality comparison for proper flat morphisms

For a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the canonical comparison
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` is an isomorphism for every derived quasicoherent object.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` is an
isomorphism for every derived quasicoherent `K`. -/
@[instance]
theorem pullbackTensorDualityMap_isIso_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
