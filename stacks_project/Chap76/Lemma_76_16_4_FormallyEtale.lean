/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale

/-!
# Formally étale morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is formally étale when it
is formally étale as a transformation of functors of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- The algebraic-space formal étaleness predicate is provided by the
canonical morphism owner. -/
#check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
