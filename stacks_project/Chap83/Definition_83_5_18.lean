/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.OrbitSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Definition 83.5.18: for `B` an algebraic space over a scheme `S` and a pre-relation
`j : R ⟶ U ⨯ U` on an algebraic space `U` over `B`, a morphism `φ : U ⟶ X` over `B` is an
orbit space for `R` if `φ` is `R`-invariant, `φ` separates `R`-orbits, and `φ` is
surjective. -/
@[stacks 0493] #check (AlgebraicGeometry.AlgebraicSpace.PreRelation.IsOrbitSpace :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B},
    PreRelation U → (U ⟶ X) → Prop)
