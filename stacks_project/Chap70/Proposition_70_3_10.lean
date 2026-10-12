/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Definition_70_3_1

/-!
# Locally of finite presentation versus limit-preserving transformations

A morphism of algebraic spaces is locally of finite presentation if and only if
it is limit preserving as a transformation of functors of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 70.3.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is locally of finite
presentation, and `f` is limit preserving as a transformation of functors. -/
@[stacks 04AK]
theorem locallyOfFinitePresentation_iff_isLimitPreserving
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ Scheme.Over.IsLimitPreserving f :=
  sorry

namespace LocallyOfFinitePresentation

/-- A locally of finite presentation morphism of algebraic spaces is limit
preserving as a transformation of functors. -/
theorem isLimitPreserving {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Scheme.Over.IsLimitPreserving f :=
  sorry

end LocallyOfFinitePresentation

/-- A morphism of algebraic spaces that is limit preserving as a transformation
of functors is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_isLimitPreserving
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.IsLimitPreserving f) : LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
