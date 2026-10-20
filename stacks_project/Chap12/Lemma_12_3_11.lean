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

section Kernel

variable [HasKernel f]

/- Lemma 12.3.11 (1): if a kernel of `f` exists, then the canonical kernel morphism
`kernel.ι f` is a monomorphism. -/
@[stacks 0E43] #check (inferInstance : Mono (kernel.ι f))

end Kernel

section Cokernel

variable [HasCokernel f]

/- Lemma 12.3.11 (2): if a cokernel of `f` exists, then the canonical cokernel morphism
`cokernel.π f` is an epimorphism. -/
@[stacks 0E43] #check (inferInstance : Epi (cokernel.π f))

end Cokernel

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/- Lemma 12.3.11 (3): the textbook coimage projection `cokernel.π (kernel.ι f)` is the owner
morphism `coimage.π f`, and it is an epimorphism. -/
@[stacks 0E43] #check (inferInstance : Epi (Abelian.coimage.π f))

end Coimage

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/- Lemma 12.3.11 (4): the textbook image inclusion `kernel.ι (cokernel.π f)` is the owner
morphism `image.ι f`, and it is a monomorphism. -/
@[stacks 0E43] #check (inferInstance : Mono (Abelian.image.ι f))

end Image

end CategoryTheory
