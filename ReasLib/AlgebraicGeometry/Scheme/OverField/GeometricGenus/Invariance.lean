/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Dimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GeometricGenus

open Scheme.Hom.ProperBirational

/-- The geometric genus of a proper scheme of dimension at most one over a field equals
that of its reduction. -/
theorem ofScheme_eq_reduction
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    ofScheme X hdim =
      ofScheme (Over.reduction X)
        ((Scheme.topologicalKrullDim_reduction X.left).le.trans hdim) := sorry

/-- Geometric genus is invariant under a proper birational morphism to a proper scheme
of dimension at most one over a field. -/
theorem ofScheme_eq_of_isProper_isBirational
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) {X' : Scheme.{u}}
    (f : X' ⟶ X.left) [IsProper f] [IsBirational f] :
    ofScheme (Over.mk (f ≫ X.hom) : SchemeOverField k)
        (topologicalKrullDim_le_one k X.hom f hdim :
          topologicalKrullDim X' ≤ 1) =
      ofScheme X hdim := sorry

/-- The geometric genus of a proper scheme of dimension at most one over a field equals
that of its normalization. -/
theorem ofScheme_normalization_eq
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    ofScheme (SchemeOverField.normalization X)
        ((SchemeOverField.Normalization.topologicalKrullDim_eq X).le.trans hdim) =
      ofScheme X hdim := sorry

end AlgebraicGeometry.GeometricGenus
