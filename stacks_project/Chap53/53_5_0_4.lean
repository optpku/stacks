/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole.CurveDegree

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open Intersection
open scoped AlgebraicGeometry

noncomputable section

universe u

/- 53.5.0.4: If `X` is a proper scheme of topological dimension at most one over a field and
`L` is invertible, then its numerical intersection `(L · X)` equals its degree `deg(L)`. -/
@[stacks 0BS0] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.lineNumber_eq_curveDegreeOfInvertible_of_topologicalKrullDim_le_one :
    {k : Type u} → [Field k] → (X : Over (Spec (CommRingCat.of k))) → [IsProper X.hom] →
      (hXdim : topologicalKrullDim X.left ≤ 1) → (L : X.left.Modules) → [Invertible L] →
      [HasExt (Sheaf (Opens.grothendieckTopology
        (⊥ : X.left.IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] →
      lineNumber k X.hom (⊥ : X.left.IdealSheafData) L =
        (curveDegreeOfInvertible X.hom hXdim L : ℚ))
