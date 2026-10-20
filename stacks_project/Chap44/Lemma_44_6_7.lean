/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.AbelMap
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 44.6.7 (1): every degree component is open in the Picard scheme. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.componentInclusion_isOpenImmersion :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℤ),
      AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.RelativePicard.componentInclusion X d).left)

/- Lemma 44.6.7 (2): every degree component is closed in the Picard scheme. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.componentInclusion_isClosedImmersion :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℤ),
      AlgebraicGeometry.IsClosedImmersion
        (AlgebraicGeometry.RelativePicard.componentInclusion X d).left)

/- Lemma 44.6.7 (3): the images of distinct degree components are disjoint. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.componentInclusion_pairwiseDisjoint :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom],
      Pairwise fun d e : ℤ ↦ Disjoint
        (Set.range (AlgebraicGeometry.RelativePicard.componentInclusion X d).left.base)
        (Set.range (AlgebraicGeometry.RelativePicard.componentInclusion X e).left.base))

/- Lemma 44.6.7 (4): the degree components cover the Picard scheme. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.iUnion_range_componentInclusion :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom],
      (⋃ d : ℤ, Set.range
        (AlgebraicGeometry.RelativePicard.componentInclusion X d).left.base) = Set.univ)

/- Lemma 44.6.7 (5): each degree component is smooth of dimension equal to the genus. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.component_smoothOfRelativeDimension :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℤ),
      AlgebraicGeometry.SmoothOfRelativeDimension (AlgebraicGeometry.Curve.genus X)
        (AlgebraicGeometry.RelativePicard.component X d).hom)

/- Lemma 44.6.7 (6): each degree component is a proper variety over `k`. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.component_properVariety :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℤ),
      AlgebraicGeometry.ProperVariety (AlgebraicGeometry.RelativePicard.component X d))

/- Lemma 44.6.7 (7): `k`-points of the degree-`d` component correspond bijectively to
invertible `𝒪_X`-modules of degree `d`, through their Picard classes. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.degreeClassToComponentPoint_bijective :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℤ),
      Function.Bijective
        (AlgebraicGeometry.RelativePicard.degreeClassToComponentPoint X d))

/- Lemma 44.6.7 (8): the degree-zero component is an open and closed subgroup scheme of
the Picard scheme. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.degreeZeroClosedSubgroup :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom],
      @AlgebraicGeometry.Scheme.ClosedSubgroup _
        (AlgebraicGeometry.RelativePicard.scheme X)
        (AlgebraicGeometry.RelativePicard.schemeGrpObj X))

#check
  (AlgebraicGeometry.RelativePicard.degreeZeroClosedSubgroup_isOpenImmersion :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom],
      AlgebraicGeometry.IsOpenImmersion
        (@AlgebraicGeometry.Scheme.ClosedSubgroup.inclusion _
          (AlgebraicGeometry.RelativePicard.scheme X)
          (AlgebraicGeometry.RelativePicard.schemeGrpObj X)
          (AlgebraicGeometry.RelativePicard.degreeZeroClosedSubgroup X)).left)

/- Lemma 44.6.7 (9): for every `d ≥ 0`, the universal effective divisor defines the
canonical Abel morphism `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.abelMap :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom] (d : ℕ),
      (AlgebraicGeometry.Hilbert.functor X d).reprX ⟶
        AlgebraicGeometry.RelativePicard.component X (d : ℤ))

/- Lemma 44.6.7 (10): `γ_d` is surjective when `d` is at least the genus. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.abelMap_surjective :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
      (d : ℕ) [Fact (AlgebraicGeometry.Curve.genus X ≤ d)],
      AlgebraicGeometry.Surjective (AlgebraicGeometry.RelativePicard.abelMap X d).left)

/- Lemma 44.6.7 (11): `γ_d` is smooth when `d ≥ 2 * genus(X) - 1`. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.abelMap_smooth :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom]
      (d : ℕ) [Fact (2 * AlgebraicGeometry.Curve.genus X - 1 ≤ d)],
      AlgebraicGeometry.Smooth (AlgebraicGeometry.RelativePicard.abelMap X d).left)

/- Lemma 44.6.7 (12): the genus-degree Abel morphism is birational. -/
@[stacks 0BA0] #check
  (AlgebraicGeometry.RelativePicard.abelMap_genus_isBirational :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Curve X]
      [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.Projective X.hom],
      AlgebraicGeometry.IsBirational
        (AlgebraicGeometry.RelativePicard.abelMap X
          (AlgebraicGeometry.Curve.genus X)).left)
