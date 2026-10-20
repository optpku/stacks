/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.26.5: the tensor product of K-flat complexes of `𝒪_X`-modules is K-flat.  The
coefficient-category owner is exposed through the method-style API `hK.tensor hL`. -/

variable (X : RingedSpace.{u})

@[stacks 079R "K-flat complexes of modules are closed under tensor products"]
#check
  CochainComplex.IsKFlat.tensor (C := Modules X)

end AlgebraicGeometry.RingedSpace
