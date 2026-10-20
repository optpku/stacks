/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Finite coproducts of finite morphisms of algebraic spaces

A finite family of finite morphisms of algebraic spaces with a common target
induces a finite morphism from the coproduct.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism from the coproduct induced by a finite family of finite
morphisms of algebraic spaces over a scheme with a common target is finite. -/
instance isFinite_coproductDesc {S : Scheme.{u}} {ι : Type v} [Finite ι] [Small.{u} ι]
    {X : ι → AlgebraicSpace S} {Y : AlgebraicSpace S} (f : ∀ i, X i ⟶ Y)
    [∀ i, IsFinite (f i)] : IsFinite (coproductDesc f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
