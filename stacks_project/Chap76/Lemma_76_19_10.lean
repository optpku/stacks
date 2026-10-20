/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.EtaleLocal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.19.10. Formal smoothness is equivalent to formal smoothness on every
commutative square with étale scheme charts. -/
@[stacks 061K] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.iff_forallEtaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.FormallySmooth f ↔
        AlgebraicGeometry.AlgebraicSpace.FormallySmooth.forallEtaleSchemeSquare f)

#check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.iff_existsSurjectiveEtaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.FormallySmooth f ↔
        AlgebraicGeometry.AlgebraicSpace.FormallySmooth.existsSurjectiveEtaleSchemeSquare f)
