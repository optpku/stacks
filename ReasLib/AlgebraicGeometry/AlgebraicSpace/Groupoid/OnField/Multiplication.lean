/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Composition of groupoids on a field

The composition morphism of a groupoid in algebraic spaces on a field is flat
and universally open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The canonical composition morphism of a groupoid in algebraic spaces whose
object space is a field spectrum is flat. -/
theorem flat_composition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.Flat G.c.left := sorry

/-- The canonical composition morphism of a groupoid in algebraic spaces whose
object space is a field spectrum is universally open. -/
theorem universallyOpen_composition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] :
    AlgebraicSpace.UniversallyOpen G.c.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
