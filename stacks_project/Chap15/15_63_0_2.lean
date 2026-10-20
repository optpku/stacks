module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Tensor
import StacksCheckRecall

/-!
# Equation 15.64.0.2 (068I)

Repository source label: 15.63.0.2.

@stack 068I
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension.Tensor

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (K L : derived R)

/- Equation 15.64.0.2 (068I): the derived tensor product of the scalar extensions of `K` and `L`
is canonically isomorphic to the scalar extension of their derived tensor product.  This is the
source-facing orientation of the canonical two-variable scalar-extension comparison. -/
@[stacks 068I]
#check
  ((comparisonIsoApp (algebraMap R A) K L).symm :
    ((extension (algebraMap R A)).prod (extension (algebraMap R A)) ⋙ derivedTensor A).obj
          (K, L) ≅
      (derivedTensor R ⋙ extension (algebraMap R A)).obj (K, L))

#print axioms comparisonIsoApp

end CategoryTheory.ModuleCat.DerivedExtension.Tensor
