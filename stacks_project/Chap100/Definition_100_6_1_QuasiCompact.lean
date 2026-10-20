module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-!
# Quasi-compact algebraic stacks

An algebraic stack is quasi-compact when it admits a surjective smooth atlas
from a quasi-compact scheme. This is the atlas form equivalent to quasi-compactness
of the space of points once that space carries its unique topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isQuasiCompact_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsQuasiCompact X ↔
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiCompact X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ CompactSpace U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsQuasiCompact.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [CompactSpace U.left], IsQuasiCompact X)

#check (AlgebraicGeometry.AlgebraicStack.instIsQuasiCompact_slice :
  ∀ {S : Scheme.{u}} (U : Over S) [CompactSpace U.left],
    IsQuasiCompact (GroupoidsOver.slice U))

end AlgebraicGeometry.AlgebraicStack
