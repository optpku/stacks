/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact.Locality
import StacksCheckRecall

/-!
# Characterizations of quasi-compact morphisms of formal algebraic spaces
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.17.3: a morphism of formal algebraic spaces is quasi-compact on
reductions if and only if all quasi-compact scheme pullbacks are quasi-compact,
all affine scheme pullbacks are quasi-compact, or some affine étale target
covering has quasi-compact pullbacks. -/
@[stacks 0AJB] #check (AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    (RX : FormalAlgebraicSpace.ReductionData X)
    (RY : FormalAlgebraicSpace.ReductionData Y) (f : X ⟶ Y),
    List.TFAE [FormalAlgebraicSpace.ReductionData.QuasiCompact RX RY f,
      FormalAlgebraicSpace.QuasiCompact.forallQuasiCompactScheme f,
      FormalAlgebraicSpace.QuasiCompact.forallAffine f,
      FormalAlgebraicSpace.QuasiCompact.existsCoverOnTarget f])
