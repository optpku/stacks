module

public import stacks_project.Chap37.Definition_37_8_1_FormallyEtale
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [IsAffine X] [IsAffine S]

/- Lemma 37.8.8: For a morphism of affine schemes, formal étaleness is equivalent
to formal étaleness of the induced map on global sections. -/
@[stacks 02HL] #check
  (AlgebraicGeometry.FormallyEtale.iff_of_isAffine (f := f) :
    FormallyEtale f ↔ f.appTop.hom.FormallyEtale)
