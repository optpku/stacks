/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Whole-scheme curve degree

This leaf records the one-dimensional comparisons between whole-scheme intersection degree,
the one-factor intersection number, and the curve degree of an ample invertible module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/-- For a proper one-dimensional scheme over a field, the whole-scheme intersection degree of
an ample invertible module equals its one-factor intersection number. -/
theorem wholeDegree_eq_lineNumber
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hXdim : topologicalKrullDim X = 1)
    (L : X.Modules) [Invertible L] [IsAmple L] :
    wholeDegree k f L hXdim = lineNumber k f (⊥ : X.IdealSheafData) L := sorry

/-- For a proper one-dimensional scheme over a field, the one-factor intersection number of an
ample invertible module equals its curve degree. -/
theorem lineNumber_eq_curveDegreeOfInvertible
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hXdim : topologicalKrullDim X = 1)
    (L : X.Modules) [Invertible L] [IsAmple L] :
    lineNumber k f (⊥ : X.IdealSheafData) L =
      (curveDegreeOfInvertible f hXdim.le L : ℚ) := sorry

/-- For a proper scheme over a field of topological Krull dimension at most one, the one-factor
intersection number of an invertible module equals its curve degree. -/
theorem lineNumber_eq_curveDegreeOfInvertible_of_topologicalKrullDim_le_one
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (hXdim : topologicalKrullDim X.left ≤ 1)
    (L : X.left.Modules) [Invertible L]
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : X.left.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] :
    lineNumber k X.hom (⊥ : X.left.IdealSheafData) L =
      (curveDegreeOfInvertible X.hom hXdim L : ℚ) := sorry

end AlgebraicGeometry.Scheme.Modules.Intersection
