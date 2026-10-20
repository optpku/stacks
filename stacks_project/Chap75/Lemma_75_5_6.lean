/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Tensor
import StacksCheckRecall

universe u

/- Lemma 75.5.6: for a scheme `S` and an algebraic space `X` over `S`, the derived
tensor product of two objects of `D_QCoh(𝒪_X)` again lies in `D_QCoh(𝒪_X)`. -/
@[stacks 08F5] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensor_mem :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (K L : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X),
    AlgebraicGeometry.AlgebraicSpace.derivedQuasiCoherentModuleProperty X
      ((CategoryTheory.DerivedCategory.DerivedTensor.Right.functor L.obj).obj K.obj))
