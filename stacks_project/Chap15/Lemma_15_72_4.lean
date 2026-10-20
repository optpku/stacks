module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Source
import StacksCheckRecall

/-!
# Tensor/internal-Hom comparison

The generic comparison is a closed braided monoidal construction. Its module-complex
specialization is owned by `CategoryTheory.CochainComplex.InternalHom.Module.tensor`.

@stack 0BYM
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.CochainComplex.InternalHom

variable {R : Type u} [CommRing R]
variable (K L M : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.72.4: the canonical map
`K ⊗ Hom^•(M, L) ⟶ Hom^•(M, K ⊗ L)`. -/
@[stacks 0BYM "tensor comparison for module-valued Hom complexes"]
#check Module.tensor (R := R) K L M

#check @Module.tensor_natural_tensor
#check @Module.tensor_natural_target
#check @Module.tensor_natural_source

section Generic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
variable (K L M : C)

/- Generic companion: the canonical map `K ⊗ [M, L] ⟶ [M, K ⊗ L]`. -/
#check tensorInternalHomComparison K L M

#check @tensorInternalHomComparison_natural_tensor
#check @tensorInternalHomComparison_natural_target
#check @tensorInternalHomComparison_natural_source

end Generic
