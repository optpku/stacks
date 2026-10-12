/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_26_1_Nagata

/-!
# Locally of finite type over Nagata algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a Nagata target has
Nagata source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- Lemma 67.26.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `Y` is Nagata and `f` is locally of finite type, then `X` is Nagata. -/
@[stacks 0BAU]
theorem isNagata {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsNagata Y] :
    IsNagata X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
