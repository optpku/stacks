/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Finite presentation morphisms of algebraic spaces are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.5 (1): A morphism of algebraic spaces which is locally of finite
presentation is locally of finite type. -/
@[stacks 0464]
instance locallyOfFiniteType_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f :=
  sorry

/-- Lemma 67.28.5 (2): A morphism of algebraic spaces of finite presentation is
of finite type. -/
@[stacks 0464]
instance finiteType_of_finitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FinitePresentation f] :
    FiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
