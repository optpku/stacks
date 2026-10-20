/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing
public import ReasLib.RingTheory.PowerSeries.Multicross
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

#check (isOrdinaryDoublePoint :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left), Prop)
#check (isOrdinaryDoublePoint_iff :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) (x : X.left),
    isOrdinaryDoublePoint X x ↔
      x ∈ closedPoints X.left ∧
        Nonempty
          (AdicCompletion (IsLocalRing.maximalIdeal (stalkRing X x)) (stalkRing X x) ≃ₐ[k]
            Multicross.ring k 2))
#check (isNode :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left), Prop)
#check (isNode_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) (x : X.left),
    isNode X x ↔
      x ∈ closedPoints X.left ∧
        ∃ xbar : (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left,
          FieldExtension.Over.toSource k (AlgebraicClosure k) X xbar = x ∧
            isOrdinaryDoublePoint
              (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) xbar)
#check (atWorstNodal : ∀ {k : Type u} [Field k] (X : SchemeOverField k), Prop)
#check (atWorstNodal.at :
  ∀ {k : Type u} [Field k] {X : SchemeOverField k},
    atWorstNodal X → ∀ (x : X.left), x ∈ closedPoints X.left →
      X.hom.SmoothAt x ∨ isNode X x)

end AlgebraicGeometry.SchemeOverField
