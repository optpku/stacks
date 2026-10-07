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
variable (K : Derived.Construction C)

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

/- A coherent construction supplies the six pieces of the derived datum explicitly; the
construction itself is an explicit parameter because this data is not a canonical typeclass
choice. Its theorem-level laws are separate from the concrete objects and morphisms below. -/
#check (X.d : X.E ⟶ X.E)
#check ((K.data X).homology : C)
#check (Derived.outer X : C)
#check (Derived.alpha X : Derived.outer X ⟶ Derived.outer X)
#check (Derived.f (K.data X) : (K.data X).homology ⟶ Derived.outer X)
#check (Derived.g (K.data X) : Derived.outer X ⟶ (K.data X).homology)

/- Lemma 12.21.2 (3) (tag `011R`): the six derived pieces form an exact couple. -/
@[stacks 011R "(3)"]
#check (K.derived X : ExactCouple C)

end ExactCouple
end CategoryTheory
