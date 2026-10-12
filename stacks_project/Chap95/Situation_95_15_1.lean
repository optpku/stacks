/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

/- Situation 95.15.1: here `S` is a scheme contained in `Sch_fppf`, `B` is an
algebraic space over `S`, `(G, m)` is a group algebraic space over `B` with
`m = μ[G.X]`, `π : X ⟶ B` is an algebraic space over `B`, and
`a = γ[G.X, X.X] : G.X ⊗ X.X ⟶ X.X` is an action of `G` on `X` over `B`. -/
@[stacks 04WL] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.Action.of :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (G : GroupAlgebraicSpace B) →
      (X : Over B) → [ModObj G.X X] → GroupAlgebraicSpace.Action G)

#check (GroupAlgebraicSpace :
  {S : Scheme.{u}} → AlgebraicSpace S → Type (u + 1))

#check (fun (S : Scheme.{u}) ↦ Scheme.fppfTopology.over S)

#check (fun {S : Scheme.{u}} {B : AlgebraicSpace S} (X : Over B) ↦ X.hom)

#check
  (fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (X : GroupAlgebraicSpace.Action G) ↦
    (γ[G.X, X.X] : G.X ⊗ X.X ⟶ X.X))

#check
  (fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) ↦
    (μ[G.X] : G.X ⊗ G.X ⟶ G.X))
