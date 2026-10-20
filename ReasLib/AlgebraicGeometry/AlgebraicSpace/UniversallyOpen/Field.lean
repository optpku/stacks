/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Morphisms of algebraic spaces over a field are universally open

A morphism of algebraic spaces over a scheme `S` to the spectrum of a field is
universally open.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme to the spectrum of a field
is universally open. -/
instance UniversallyOpen.of_over_field {S : Scheme.{u}} {X : AlgebraicSpace S}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (p : X ⟶ ofOver (Over.mk σ)) : UniversallyOpen p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
