/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.10.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is a monomorphism if it is an injective map of sheaves, i.e. a monomorphism in the
category of fppf sheaves on `Over S`. Equivalently, `f` is a categorical
monomorphism iff each component `f.app T` is injective. -/
@[stacks 042L] #check (AlgebraicGeometry.AlgebraicSpace.mono_iff_injective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Mono f ↔ ∀ (T : (Over S)ᵒᵖ), Function.Injective (f.app T))
