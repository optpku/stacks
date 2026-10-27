/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteType.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Composition

/-!
# Purity of pushforwards along closed immersions

A finite type quasi-coherent module on a closed subspace is (universally) pure
above a point if and only if its pushforward is.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A finite type quasi-coherent module on a closed subspace is pure above a
point of the base if and only if its pushforward is pure above that point. -/
theorem isPureAlong_pushforward_iff_of_isClosedImmersion
    {Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] (y : Points Y) :
    G.IsPureAlong (i ≫ f) y ↔ ((pushforward i).obj G).IsPureAlong f y :=
  sorry

/-- A finite type quasi-coherent module on a closed subspace is universally
pure above a point of the base if and only if its pushforward is universally
pure above that point. -/
theorem isUniversallyPureAlong_pushforward_iff_of_isClosedImmersion
    {Z : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) [G.IsQuasicoherent]
    [G.IsFiniteType] (y : Points Y) :
    G.IsUniversallyPureAlong (i ≫ f) y ↔
      ((pushforward i).obj G).IsUniversallyPureAlong f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
