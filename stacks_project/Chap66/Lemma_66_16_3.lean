/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 66.16.3: étaleness is equivalent to the source-atlas, target-atlas,
and commutative-square tests for an arbitrary morphism of algebraic spaces. -/
@[stacks 03FS] #check (AlgebraicGeometry.AlgebraicSpace.Etale.tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [AlgebraicSpace.Etale f, AlgebraicSpace.Etale.existsOnSource f,
      AlgebraicSpace.Etale.existsOnTarget f, AlgebraicSpace.Etale.existsSquare f])
