/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Precoverage

/-!
# Syntomic morphisms are syntomic local on the source

Syntomicity of morphisms of algebraic spaces is local on the source for the
syntomic precoverage.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- Syntomicity of morphisms of algebraic spaces is local on the source for the
syntomic precoverage. -/
instance isLocalAtSourceSyntomic {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtSource
      (@Syntomic S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Syntomic S)) :=
  sorry

/-- A morphism of algebraic spaces is syntomic if and only if it remains so after
precomposition with every member of a syntomic covering of the source. -/
theorem iff_forall_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (𝒰 : (precoverage (@Syntomic S)).ZeroHypercover X) :
    Syntomic f ↔ ∀ i, Syntomic (𝒰.f i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic
