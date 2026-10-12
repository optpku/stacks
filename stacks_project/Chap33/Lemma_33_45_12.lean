/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.CurveDegree

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 33.45.12 (1): the intersection with a closed subscheme of dimension at most one is the
degree of the restricted invertible module. -/
@[stacks 0BEY] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.lineNumber_eq_curveDegreeOfInvertible_pullback :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (Z : X.IdealSheafData)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (L : X.Modules) [Scheme.Modules.Invertible L]
      (hZdim : topologicalKrullDim Z.subscheme ≤ 1),
      Scheme.Modules.Intersection.lineNumber k f Z L =
        (Scheme.Modules.curveDegreeOfInvertible (Z.subschemeι ≫ f) hZdim
          ((Scheme.Modules.pullback Z.subschemeι).obj L) : ℚ))

/- Lemma 33.45.12 (2): for an ample invertible module and a one-dimensional closed subscheme,
the intersection degree is the degree of the restricted module. -/
@[stacks 0BEY] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.degree_eq_curveDegreeOfInvertible_pullback_of_topologicalKrullDim_eq_one :
    ∀ (k : Type u) [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L : X.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      (Z : X.IdealSheafData)
      [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
      (hZdim : topologicalKrullDim Z.subscheme = 1),
      Scheme.Modules.Intersection.degree k f L Z hZdim =
        (Scheme.Modules.curveDegreeOfInvertible (Z.subschemeι ≫ f) hZdim.le
          ((Scheme.Modules.pullback Z.subschemeι).obj L) : ℚ))
