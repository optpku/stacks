/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth

@[expose] public section

universe u v

/- Definition 34.5.1: A smooth covering of a scheme `T` is an indexed family of
morphisms to `T` that are smooth and whose images jointly cover `T`. -/
@[stacks 021Z] #check
  (AlgebraicGeometry.Scheme.SmoothCovering :
    {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
      (ι → CategoryTheory.Over T) → Prop)

#check
  (AlgebraicGeometry.Scheme.smoothCovering_iff :
    {T : AlgebraicGeometry.Scheme.{u}} → {ι : Type v} →
      (family : ι → CategoryTheory.Over T) →
        AlgebraicGeometry.Scheme.SmoothCovering family ↔
          (∀ i : ι, AlgebraicGeometry.Smooth (family i).hom) ∧
            Function.Surjective
              (AlgebraicGeometry.Scheme.smoothCoveringPointMap family))
