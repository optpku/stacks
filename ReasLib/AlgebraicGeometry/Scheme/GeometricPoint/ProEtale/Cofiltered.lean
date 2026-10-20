/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.FieldTheory.IsAlgClosed.Basic

open CategoryTheory Opposite

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme.GeometricPoint.ProetaleNeighborhood

/-- The category of weakly étale neighborhoods equipped with a lift of an
algebraically closed field-valued point of a scheme is cofiltered. -/
instance instIsCofiltered {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (point : Spec (.of K) ⟶ S) :
    IsCofiltered ((ProEt.forget S ⋙ coyoneda.obj (op (Over.mk point))).Elements) := sorry

end AlgebraicGeometry.Scheme.GeometricPoint.ProetaleNeighborhood
