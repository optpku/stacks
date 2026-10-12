/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Quasi-separated morphisms with uniqueness are separated

A quasi-separated morphism of algebraic spaces that satisfies uniqueness in the
valuative criterion is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

/-- Lemma 67.43.2 (Valuative criterion separatedness): Let `S` be a scheme. Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Assume `f` is
quasi-separated and satisfies the uniqueness part of the valuative criterion.
Then `f` is separated. -/
@[stacks 03KV]
theorem of_valuativeCriterion {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [ValuativeCriterion.Uniqueness f] : Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
