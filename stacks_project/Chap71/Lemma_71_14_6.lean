/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Locality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u

/- Lemma 71.14.6: relative ampleness of an invertible module is equivalent to
scheme representability and relative ampleness after every scheme base change,
every affine scheme base change, or some surjective étale scheme base change. -/
@[stacks 0D36] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (L : X.Modules)
      [isInvertibleObject L],
      List.TFAE [RelativelyAmple f L, RelativelyAmple.forallScheme f L,
        RelativelyAmple.forallAffine f L, RelativelyAmple.existsSurjectiveEtale f L])
