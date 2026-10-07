module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Presentation.Finite

/-!
# Weak Serre classes from finite generator presentations

The standard presentation argument reduces closure under arbitrary kernels to kernels of maps
between finite coproducts of generators.  Together with cokernel and extension closure this gives
a reusable weak-Serre criterion.
-/

@[expose] public section

open CategoryTheory.Limits

universe u₂ v₂ u₁ v₁

namespace CategoryTheory.Functor.FiniteCokernelPresentation.HasKernels

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasFiniteCoproducts D]
variable {G : C ⥤ D} {B : Set C}

/-- If finite generator presentations are closed under cokernels and extensions, the
generator-kernel condition makes them a weak Serre class. -/
theorem isWeakSerreClass
    (h_kernels : FiniteCokernelPresentation.HasKernels G B)
    (h_cokernels : (G.finiteCokernelPresentation B).IsClosedUnderCokernels)
    (h_extensions : (G.finiteCokernelPresentation B).IsClosedUnderExtensions) :
    ObjectProperty.IsWeakSerreClass (G.finiteCokernelPresentation B) := sorry

end CategoryTheory.Functor.FiniteCokernelPresentation.HasKernels
