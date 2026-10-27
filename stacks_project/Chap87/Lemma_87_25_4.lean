/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective.Locality
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.25.4: surjectivity of a morphism of formal algebraic spaces is
 equivalent to the scheme, affine scheme, affine étale covering, and
 surjective formal-space target tests. -/
@[stacks 0GHS] #check (AlgebraicGeometry.FormalAlgebraicSpace.Surjective.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [hX : AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [hY : AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    (RX : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData X)
    (RY : AlgebraicGeometry.FormalAlgebraicSpace.ReductionData Y) (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.Surjective RX RY f,
      AlgebraicGeometry.FormalAlgebraicSpace.Surjective.forallScheme f,
      AlgebraicGeometry.FormalAlgebraicSpace.Surjective.forallAffine f,
      AlgebraicGeometry.FormalAlgebraicSpace.Surjective.existsCoverOnTarget f,
      AlgebraicGeometry.FormalAlgebraicSpace.Surjective.existsSurjectiveOnTarget RY f])
