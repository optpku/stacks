/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_44_2_RegularImmersion
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Koszul-regular immersions of algebraic spaces are local complete intersections

A Koszul-regular immersion of algebraic spaces over a scheme is a local
complete intersection morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.48.7: Let `S` be a scheme. A Koszul-regular immersion of algebraic
spaces over `S` is a local complete intersection morphism. -/
@[stacks 0CHK]
instance IsKoszulRegularImmersion.isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (i : X ⟶ Y) [IsKoszulRegularImmersion i] :
    IsLocalCompleteIntersection i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
