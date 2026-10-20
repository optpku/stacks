module

import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient.Bounded.Computation
import ReasLib.CategoryTheory.Functor.Kernel.Lift
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.17.3

The derived Serre quotient and its bounded restrictions are owned by
`SerreClassLocalization.Derived`.  The namespace separates the canonical
quotient, its kernel, and the `Plus`, `Minus`, and `Bounded` restrictions.
-/

open CategoryTheory

/- Lemma 13.17.3: if the Serre quotient admits a fully faithful left adjoint,
its derived functor is the Verdier localization by objects with cohomology in
the Serre class. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.isLocalization

/- Companion check: the localization at the canonical functor kernel is
available before identifying that kernel with cohomology in the Serre class. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.Kernel.isLocalization

/- Companion checks: the homology comparison is naturally functorial, while
its objectwise component and kernel identification remain short interfaces. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.homologyFunctorIso

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.homologyIso

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.homologyIso_hom_naturality

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.homologyIso_inv_naturality

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Quotient.kernel_eq

/- Lemma 13.17.3 (bounded-below): the restricted functor realizes the
corresponding Verdier localization of `D⁺(A)`. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.isLocalization

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.functor

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.compιIso

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.functor.obj_obj

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Plus.Quotient.functor.map_hom

/- Lemma 13.17.3 (bounded-above): the restricted functor realizes the
corresponding Verdier localization of `D⁻(A)`. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.isLocalization

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.functor

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.compιIso

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.functor.obj_obj

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Minus.Quotient.functor.map_hom

/- Lemma 13.17.3 (bounded): the restricted functor realizes the corresponding
Verdier localization of `Dᵇ(A)`. -/
@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.isLocalization

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.functor

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.compιIso

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.functor.obj_obj

@[stacks 06XM]
#check @ObjectProperty.SerreClassLocalization.Derived.Bounded.Quotient.functor.map_hom

/- Companion check: restricting a functor's codomain to a full subcategory
does not change its objectwise kernel. -/
@[stacks 06XM] #check @Functor.Kernel.lift_eq
