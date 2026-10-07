module

public import Mathlib.CategoryTheory.Abelian.Subobject
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C} (f : X ⟶ Y)

/- Definition 12.5.3 (1) [010B]: the textbook condition that `f` is injective is represented
canonically by the vanishing of its kernel.  In an abelian category this is equivalent to
`Mono f`, so no parallel predicate is introduced. -/
@[stacks 010B]
#check (IsZero (kernel f) : Prop)

#check (Preadditive.mono_iff_isZero_kernel f : Mono f ↔ IsZero (kernel f))

/- Definition 12.5.3 (2) [010B]: the textbook condition that `f` is surjective is represented
canonically by the vanishing of its cokernel, equivalently by `Epi f`. -/
#check (IsZero (cokernel f) : Prop)

#check (Preadditive.epi_iff_isZero_cokernel f : Epi f ↔ IsZero (cokernel f))

/- A monomorphism is represented by its canonical bundled subobject, rather than by an
existence-only relation between its source and target objects. -/
section

variable [Mono f]

#check (Subobject.mk f : Subobject Y)

end

/- Quotient objects are modeled dually by subobjects in the opposite category.  In an abelian
category this agrees with the ordinary subobject model through the canonical equivalence. -/
#check Abelian.subobjectIsoSubobjectOp X

end
