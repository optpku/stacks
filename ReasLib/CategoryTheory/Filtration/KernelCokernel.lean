/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Induced
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Kernels and Cokernels of Filtered Morphisms

This file provides the induced-filtered kernel and quotient-filtered cokernel of a morphism of
filtered objects under precisely the ambient limits, colimits, and image assumptions they use.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C]
variable {A B : FilteredObject C}

section Kernel

variable [HasZeroMorphisms C] [HasPullbacks C] [HasKernels C]

/-- The filtered kernel of a morphism, with the filtration induced from its source. -/
noncomputable def kernel (f : A ⟶ B) : FilteredObject C :=
  A.subobject (kernelSubobject f.hom)

/-- The canonical inclusion of a filtered kernel into its source. -/
noncomputable def kernelι (f : A ⟶ B) : kernel f ⟶ A :=
  A.subobjectι (kernelSubobject f.hom)

/-- The filtered kernel inclusion followed by the original morphism is zero. -/
theorem kernelι_comp (f : A ⟶ B) : kernelι f ≫ f = 0 := sorry

end Kernel

section Cokernel

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C]

/-- The filtered cokernel of a morphism, with the quotient filtration induced from its target. -/
noncomputable def cokernel (f : A ⟶ B) : FilteredObject C :=
  B.pushforward (Limits.cokernel.π f.hom)

/-- The canonical projection from the target to its filtered cokernel. -/
noncomputable def toCokernel (f : A ⟶ B) : B ⟶ cokernel f :=
  B.toPushforward (Limits.cokernel.π f.hom)

/-- The original filtered morphism followed by its cokernel projection is zero. -/
theorem comp_toCokernel (f : A ⟶ B) : f ≫ toCokernel f = 0 := sorry

end Cokernel

end CategoryTheory.FilteredObject.Hom
