/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerComparison

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.6.1. Étale extension by zero of the constant integers carries a
fibre product to the tensor product, by pairing Hom-generators, and a disjoint
union to the binary direct sum. -/
@[stacks 0722] #check
  (AlgebraicGeometry.AlgebraicSpace.ExtensionByZeroInteger.tensorComparison_isIso :
    ∀ {S : Scheme.{u}} {X U1 U2 : AlgebraicSpace S}
      (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) [HasPullback f1 f2] [Etale f1] [Etale f2],
      IsIso (AlgebraicGeometry.AlgebraicSpace.ExtensionByZeroInteger.tensorComparison f1 f2))

#check (AlgebraicGeometry.AlgebraicSpace.ExtensionByZeroInteger.coprodComparison_isIso :
  ∀ {S : Scheme.{u}} {X U1 U2 : AlgebraicSpace S}
    (f1 : U1 ⟶ X) (f2 : U2 ⟶ X) [Etale f1] [Etale f2],
    IsIso (AlgebraicGeometry.AlgebraicSpace.ExtensionByZeroInteger.coprodComparison f1 f2))
