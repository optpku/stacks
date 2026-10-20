/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct.Sequential.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor.Triangulated
import StacksCheckRecall

/-!
# Remark 15.88.10

@stack 091J
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/- Remark 15.88.10: for a fixed derived sequential inverse system `E`, the source functor
`K ↦ R lim (Δ(K) ⊗ E)` is the generic composite `DerivedLimit.tensorRight E`. Its factors are the
derived constant-diagram functor, fixed-factor derived tensoring, and the total right derived
sequential inverse limit. -/
@[stacks 091J] #check DerivedLimit.tensorRight (A := ModuleCat A)

/- Remark 15.88.10: the shift comparison and triangulated exactness of this composite are owned
by the corresponding generic model-dependent instances. -/
#check @DerivedLimit.tensorRight_commShift
#check @DerivedLimit.tensorRight_isTriangulated

end CategoryTheory.ModuleCat
