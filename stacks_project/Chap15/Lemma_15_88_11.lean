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
# Lemma 15.88.11

@stack 091K
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/- Lemma 15.88.11: for a fixed `K : DerivedCategory (ModuleCat A)`, the functor sending a
derived sequential inverse system `E` to the derived inverse limit of the tensor with the
constant system on `K` is the generic `DerivedLimit.tensorLeft K`. -/
@[stacks 091K] #check DerivedLimit.tensorLeft (A := ModuleCat A)

/- Lemma 15.88.11: the generic fixed-left tensor-derived-limit API supplies the shift comparison,
triangulated exactness, and distinguished-triangle image statement required by the source. -/
#check @DerivedLimit.tensorLeft_commShift
#check @DerivedLimit.tensorLeft_isTriangulated
#check @DerivedLimit.tensorLeft_map_distinguished

end CategoryTheory.ModuleCat
