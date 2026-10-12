/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard

universe u

/- Definition 59.20.4: for an affine target, a standard τ-cover is a finite
affine family whose chart images jointly cover the target and whose maps satisfy
the chart condition selected by `τ`; this is the existing predicate
`StandardTopology.IsCover`. -/
@[stacks 03X9] #check (AlgebraicGeometry.StandardTopology.IsCover :
  ∀ {T : AlgebraicGeometry.Scheme.{u}}
    (τ : AlgebraicGeometry.StandardTopology),
    AlgebraicGeometry.AffineFamilyOver T → Prop)
