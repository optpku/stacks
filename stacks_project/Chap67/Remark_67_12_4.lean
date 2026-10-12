/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Remark_67_12_4_Coborder

/-!
# Closed-then-open factorizations of immersions of algebraic spaces

Any immersion of algebraic spaces factors as a closed immersion followed by an
open immersion, by lifting through the coborder of its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsImmersion

/-- Remark 67.12.4: Let `S` be a scheme. Let `f : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Since `f` is a monomorphism we may identify `|Z|`
with its image in `|X|`. The boundary
`∂|Z| = closure (Set.range (Points.map f)) \ Set.range (Points.map f)`
is closed, and `∂Z` is the reduced induced closed subspace of `X` on that set
(Definition 66.12.5). Then `|Z|` is closed in `|X| \ |∂Z| = |X \ ∂Z|`, so `f`
factors as a closed immersion followed by an open immersion. The reverse order
fails in general (Example 29.3.4). -/
@[stacks 04CE]
theorem exists_closedImmersion_openImmersion_factorization {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (f : Z ⟶ X) [IsImmersion f] :
    ∃ (U : AlgebraicSpace S) (c : Z ⟶ U) (o : U ⟶ X),
      IsClosedImmersion c ∧ IsOpenImmersion o ∧ c ≫ o = f :=
  sorry

/-- A morphism of algebraic spaces is an immersion if and only if it factors as
a closed immersion followed by an open immersion. -/
theorem iff_exists {S : Scheme.{u}} {Z X : AlgebraicSpace S} (f : Z ⟶ X) :
    IsImmersion f ↔
      ∃ (U : AlgebraicSpace S) (c : Z ⟶ U) (o : U ⟶ X),
        IsClosedImmersion c ∧ IsOpenImmersion o ∧ c ≫ o = f :=
  sorry

end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
