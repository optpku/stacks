/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Smooth morphisms of algebraic spaces are locally of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.37.6: A smooth morphism of algebraic spaces is locally of finite type. -/
@[stacks 06MH]
instance locallyOfFiniteType_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] : LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
