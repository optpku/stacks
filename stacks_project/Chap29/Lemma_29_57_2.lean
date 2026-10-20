/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.FieldValuedPoint

open CategoryTheory Limits
open AlgebraicGeometry
open scoped BigOperators

universe u

/- Lemma 29.57.2: for a scheme morphism `f` and a natural number `n`, the fibre degrees of `f`
are bounded by `n` if and only if every pullback along a field-valued point is finite of degree
at most `n`. -/
@[stacks 03J5] #check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_iff_forall_fieldValuedPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ),
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n ↔
        ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
          AlgebraicGeometry.IsFinite (pullback.snd f g) ∧
            AlgebraicGeometry.Scheme.Hom.fieldValuedPointPullbackDegree f g ≤ n)

/- The same uniform field-valued-point hypothesis implies universal boundedness of the fibres. -/
#check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_of_forall_fieldValuedPoints :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ},
      (∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
        AlgebraicGeometry.IsFinite (pullback.snd f g) ∧
          AlgebraicGeometry.Scheme.Hom.fieldValuedPointPullbackDegree f g ≤ n) →
        AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f)

/- A fibre-degree bound also bounds the number of points in every field-valued pullback. -/
#check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy.finite_pullback_and_natCard_le :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ},
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n →
        ∀ {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y),
          Finite (pullback f g : Scheme) ∧ Nat.card (pullback f g : Scheme) ≤ n)

/- For an exhaustive finite set of pullback points, the sum of their residue degrees is bounded
by the same fibre-degree bound. -/
#check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy.sum_fieldValuedPointPullbackResidueDegree_le :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} {n : ℕ},
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n →
        ∀ {k : Type u} [Field k] (g : Spec (CommRingCat.of k) ⟶ Y)
          (s : Finset (pullback f g : Scheme)),
          (∀ x, x ∈ s) →
            ∑ x ∈ s,
              AlgebraicGeometry.Scheme.Hom.fieldValuedPointPullbackResidueDegree f g x ≤ n)
