module

import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient
import StacksCheckRecall

@[expose] public section

/- Lemma 13.17.2 (`06XL`): essential surjectivity of the Serre quotient on complexes and derived
categories is a neutral ReasLib owner.  The chapter entry deliberately exposes no recursive
choice data or proof-local repair structures. -/
@[stacks 06XL] #check
  @CategoryTheory.ObjectProperty.SerreClassLocalization.Cochain.Quotient.essSurj
@[stacks 06XL] #check
  @CategoryTheory.ObjectProperty.SerreClassLocalization.Derived.Quotient.essSurj
