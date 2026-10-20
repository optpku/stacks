/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Images
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)

section

variable [HasKernel f]

/-
Definition 12.3.9 (kernel): the textbook kernel construction in a preadditive category is the
canonical owner object `kernel f` with structure morphism `kernel.ι f`, characterized by the
universal property `kernelIsKernel f`; the owner API itself only needs zero morphisms.
-/
@[stacks 0106] #check kernelIsKernel f
@[stacks 0106] #check kernel.ι f
#check kernel.condition f

end

section

variable [HasCokernel f]

/-
Definition 12.3.9 (cokernel): the textbook cokernel construction in a preadditive category is the
canonical owner object `cokernel f` with structure morphism `cokernel.π f`, characterized by the
universal property `cokernelIsCokernel f`; the owner API itself only needs zero morphisms.
-/
@[stacks 0106] #check cokernelIsCokernel f
@[stacks 0106] #check cokernel.π f
#check cokernel.condition f

end

section

variable [HasKernel f]
variable [HasCokernel (kernel.ι f)]

/- Definition 12.3.9 (coimage): the textbook coimage construction, stated for preadditive
categories, is the canonical owner object `Abelian.coimage f` with structure morphism
`Abelian.coimage.π f`. -/
@[stacks 0106] #check cokernelIsCokernel (kernel.ι f)
@[stacks 0106] #check Abelian.coimage.π f

end

section

variable [HasCokernel f]
variable [HasKernel (cokernel.π f)]

/- Definition 12.3.9 (image): the textbook image construction, stated for preadditive categories,
is the canonical owner object `Abelian.image f` with structure morphism `Abelian.image.ι f`. -/
@[stacks 0106] #check kernelIsKernel (cokernel.π f)
@[stacks 0106] #check Abelian.image.ι f

end

end CategoryTheory
