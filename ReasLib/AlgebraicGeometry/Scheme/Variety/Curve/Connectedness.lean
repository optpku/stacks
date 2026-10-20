/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.KrullDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Over an algebraically closed field, a reduced connected projective scheme whose
irreducible components all have topological Krull dimension `1` has first cohomology
of the curve dualizing module of dimension at most `1`. -/
theorem cohomologyFinrank_curveDualizingModule_le_one_of_connectedSpace
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [IsReduced X.left] [Projective X.hom] [ConnectedSpace X.left]
    (h_components : ∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1) :
    Scheme.Hom.cohomologyFinrank X.hom (curveDualizingModule X.hom) 1 ≤ 1 := sorry

/-- Over an algebraically closed field, a reduced projective scheme whose irreducible
components all have topological Krull dimension `1` is disconnected if the first
cohomology of its curve dualizing module has dimension greater than `1`. -/
theorem not_connectedSpace_of_one_lt_cohomologyFinrank_curveDualizingModule
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [IsReduced X.left] [Projective X.hom]
    (h_components : ∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1)
    (h_dim : 1 < Scheme.Hom.cohomologyFinrank X.hom (curveDualizingModule X.hom) 1) :
    ¬ ConnectedSpace X.left := sorry

end AlgebraicGeometry.SchemeOverField
