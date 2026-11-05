/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Derived
public import ReasLib.CategoryTheory.Homology.ExactCouple.Subobjects
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (X : ExactCouple C)

/- Lemma 12.21.2 (1) (tag `011R`): `kernel d` is both the inverse image of `kernel g`
and the inverse image of `image α` under `f`. -/
@[stacks 011R "(1)"]
#check (Kernel.d_eq_preimage_image_alpha X :
  kernelSubobject X.d = (Subobject.pullback X.f).obj (imageSubobject X.α))

#check (Kernel.d_eq_pullback_g X :
  kernelSubobject X.d = (Subobject.pullback X.f).obj (kernelSubobject X.g))

/- Lemma 12.21.2 (2) (tag `011R`): `image d` is both the image under `g` of `image f`
and the image under `g` of `kernel α`. -/
@[stacks 011R "(2)"]
#check (Image.d_eq_g_on_kernel_alpha X :
  imageSubobject X.d = imageSubobject ((kernelSubobject X.α).arrow ≫ X.g))

#check (Image.d_eq_g_on_image_f X :
  imageSubobject X.d = imageSubobject ((imageSubobject X.f).arrow ≫ X.g))

/- The derived datum is obtained canonically from the image, kernel, and homology universal
properties. Its exactness laws are proved for this construction, rather than supplied by a caller. -/
#check (X.d : X.E ⟶ X.E)
#check ((Derived.data X).homology : C)
#check (Derived.outer X : C)
#check (Derived.alpha X : Derived.outer X ⟶ Derived.outer X)
#check (Derived.f (Derived.data X) : (Derived.data X).homology ⟶ Derived.outer X)
#check (Derived.g (Derived.data X) : Derived.outer X ⟶ (Derived.data X).homology)

/- Lemma 12.21.2 (3) (tag `011R`): the six derived pieces form an exact couple. -/
@[stacks 011R "(3)"]
#check (Derived.laws X : Derived.Laws (Derived.data X))
#check (Derived.derived X : ExactCouple C)

end ExactCouple
end CategoryTheory
