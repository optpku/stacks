/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_38_8_Unramified
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Unramified morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.38.6: An unramified morphism of algebraic spaces is locally of finite type. -/
@[stacks 05VZ]
instance locallyOfFiniteType_of_unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
