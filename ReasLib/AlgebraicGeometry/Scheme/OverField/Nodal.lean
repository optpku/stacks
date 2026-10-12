/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Multicross

/-!
# Nodal points on schemes over a field

This file defines ordinary double points over an algebraically closed field,
nodes over an arbitrary field, and the pointwise at-worst-nodal condition.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A closed point over an algebraically closed field is an ordinary double point when its
completed local ring is the two-branch multicross ring. -/
def isOrdinaryDoublePoint {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) : Prop :=
  x ∈ closedPoints X.left ∧
    Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
        Multicross.ring k 2)

/-- The defining closedness and completed-local-ring characterization of an ordinary double
point. -/
theorem isOrdinaryDoublePoint_iff {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) (x : X.left) :
    isOrdinaryDoublePoint X x ↔
      x ∈ closedPoints X.left ∧
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            Multicross.ring k 2) := sorry

/-- An ordinary double point is exactly a two-branch multicross point. -/
theorem ordinaryDoublePoint_iff_multicrossPoint_two
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left) :
    isOrdinaryDoublePoint X x ↔ isMulticrossPoint X x 2 := sorry

/-- A multicross singularity on a reduced algebraic one-dimensional Gorenstein scheme over
an algebraically closed field is an ordinary double point. -/
@[stacks 0CDZ]
theorem isOrdinaryDoublePoint_of_isMulticrossSingularity
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Algebraic X]
    [IsReduced X.left] (h_dimension : topologicalKrullDim X.left = 1)
    [Scheme.Gorenstein X.left] (x : X.left) (hx : isMulticrossSingularity X x) :
    isOrdinaryDoublePoint X x := sorry

/-- A node over `k` is a closed point admitting an ordinary double point above it after base
change to `AlgebraicClosure k`. -/
def isNode {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left) : Prop :=
  x ∈ closedPoints X.left ∧
    ∃ xbar : (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
      FieldExtension.Over.toSource k (AlgebraicClosure k) X xbar = x ∧
        isOrdinaryDoublePoint (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) xbar

/-- The defining closedness and algebraic-closure lift characterization of a node. -/
theorem isNode_iff {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left) :
    isNode X x ↔
      x ∈ closedPoints X.left ∧
        ∃ xbar : (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
          FieldExtension.Over.toSource k (AlgebraicClosure k) X xbar = x ∧
            isOrdinaryDoublePoint
              (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) xbar := sorry

/-- A scheme over a field has at-worst-nodal singularities when each closed point is smooth
over the field or is a node. -/
def atWorstNodal {k : Type u} [Field k] (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, x ∈ closedPoints X.left → X.hom.SmoothAt x ∨ isNode X x

/-- Specialize the at-worst-nodal condition at a closed point. -/
theorem atWorstNodal.at {k : Type u} [Field k] {X : SchemeOverField k}
    (hX : atWorstNodal X) (x : X.left) (hx : x ∈ closedPoints X.left) :
    X.hom.SmoothAt x ∨ isNode X x := sorry

end AlgebraicGeometry.SchemeOverField
