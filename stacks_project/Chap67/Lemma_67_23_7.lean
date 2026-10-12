/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Immersions of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.23.7: An immersion of algebraic spaces is locally of finite type. -/
@[stacks 06ED]
instance locallyOfFiniteType_of_isImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsImmersion f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
