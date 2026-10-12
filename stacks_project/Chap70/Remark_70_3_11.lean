/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap70.Definition_70_3_1

/-!
# Locally of finite presentation of an algebraic space over its base

An algebraic space `X` over a scheme `S` is locally of finite presentation over
`S` if and only if its functor of points preserves directed affine limits.
Surjectivity of the comparison `colim X(T_i) ⟶ X(T)` on directed inverse limits
of affine schemes over `S` already implies that property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 70.3.11 (1): Let `S` be a scheme. Let `X` be an algebraic space over
`S`. Then `X` is locally of finite presentation over `S` if and only if `X`, as
a functor `(Over S)ᵒᵖ ⥤ Type`, is limit preserving. Compare with Limits,
Remark 32.6.2. -/
@[stacks 05N0]
theorem locallyOfFinitePresentation_iff_preservesDirectedAffineLimits
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    LocallyOfFinitePresentation (toBase X) ↔
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  sorry

namespace LocallyOfFinitePresentation

/-- A locally of finite presentation algebraic space over `S` has a
limit-preserving functor of points. -/
theorem preservesDirectedAffineLimits_toBase {S : Scheme.{u}} (X : AlgebraicSpace S)
    [LocallyOfFinitePresentation (toBase X)] :
    Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  sorry

end LocallyOfFinitePresentation

/-- If the functor of points of an algebraic space over `S` preserves directed
affine limits, then the structure morphism is locally of finite presentation. -/
theorem locallyOfFinitePresentation_of_preservesDirectedAffineLimits
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints) :
    LocallyOfFinitePresentation (toBase X) :=
  sorry

/-- The structure morphism of `X` over `S` is limit preserving as a transformation
of functors if and only if the functor of points of `X` preserves directed affine
limits. -/
theorem isLimitPreserving_toBase_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Scheme.Over.IsLimitPreserving (toBase X) ↔
      Scheme.Over.PreservesDirectedAffineLimits S X.functorOfPoints :=
  sorry

/-- Remark 70.3.11 (2): In the criterion of Remark 70.3.11 (1), it suffices that
the comparison `colim X(T_i) ⟶ X(T)` is surjective whenever `T = lim T_i` is a
directed inverse limit of affine schemes over `S`. -/
@[stacks 05N0]
theorem locallyOfFinitePresentation_toBase_of_surjective_on_affine_stages
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hsurj :
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D),
        IsLimit c →
          (∀ i : I, IsAffine (D.obj i).left) →
          Function.Surjective
            (colimit.desc _ (X.functorOfPoints.mapCocone c.op))) :
    LocallyOfFinitePresentation (toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
