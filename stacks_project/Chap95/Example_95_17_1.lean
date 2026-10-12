/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.Example_95_17_1_Comparison
public import stacks_project.Chap95.Example_95_17_1_Coproduct
public import stacks_project.Chap95.Example_95_17_1_FixedLocus

/-!
# Example 95.17.1

The inertia stack of `[[X/G]]` for a commutative abstract group action on a scheme over `S`
is the stack coproduct of the quotient stacks `[[X^g/G]]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.QuotientStack.InertiaCoprod

noncomputable section

universe u

/-- Example 95.17.1: if `G` is a commutative group acting on a scheme `X` over `S` by
automorphisms `ρ : G →* Aut X`, then the inertia stack of `[[X/G]]` is the stack coproduct of
the family `[[X^g/G]]`, where `X^g` is the scheme-theoretic fibre product of `(1, 1)` with
`(g, 1)`. The comparison `toInertia ρ` is a stackification on `(Sch/S)_fppf`. -/
@[stacks 0374, instance]
instance inertia_coprod {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S) (toInertia ρ) :=
  sorry
