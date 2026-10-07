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

/- 53.5.0.5 (1): In dimension one, whole-scheme intersection degree is the one-factor
intersection number; this item does not assert the same equality in dimension zero. -/
@[stacks 0BS1] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.wholeDegree_eq_lineNumber :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hXdim : topologicalKrullDim X = 1) (L : X.Modules) [Invertible L] [IsAmple L],
      wholeDegree k f L hXdim = lineNumber k f (⊥ : X.IdealSheafData) L)

/- 53.5.0.5 (2): In dimension one, the one-factor intersection number is the curve degree of
the ample invertible module; this item does not assert a dimension-zero comparison. -/
@[stacks 0BS1] #check
  (AlgebraicGeometry.Scheme.Modules.Intersection.lineNumber_eq_curveDegreeOfInvertible :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hXdim : topologicalKrullDim X = 1) (L : X.Modules) [Invertible L] [IsAmple L],
      lineNumber k f (⊥ : X.IdealSheafData) L =
        (curveDegreeOfInvertible f hXdim.le L : ℚ))
