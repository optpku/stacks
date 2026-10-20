module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.QuotientStack.Inertia.Comparison

/-!
# Example 95.17.1

The inertia stack of `[[X/G]]` for a commutative abstract group action on a scheme over `S`
is the stack coproduct of the quotient stacks `[[X^g/G]]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
universe u

/- Example 95.17.1: the inertia of a quotient by a commutative group is the stack coproduct
of the quotient stacks of the scheme-theoretic diagonal–graph fixed loci. -/
@[stacks 0374] #check (AlgebraicGeometry.QuotientStack.InertiaCoprod.inertia_coprod :
  ∀ {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S} (ρ : G →* Aut X),
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.QuotientStack.InertiaCoprod.toInertia ρ))

