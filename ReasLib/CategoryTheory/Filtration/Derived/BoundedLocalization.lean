module

public import ReasLib.CategoryTheory.Filtration.Derived.Bounded
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedQuasiIso
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded localizations of finite filtered complexes

The three quotient functors are concrete lifts into full subcategories of the finite filtered
derived category.  Their universal outgoing lifts live in `BoundedLocalization.Lift`, while
triangulated structures live in `BoundedLocalization.Triangulated`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.Quotient

/-- The ambient finite filtered quotient sends bounded-below complexes to bounded-below objects. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
theorem objMem (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    Plus.property C h_inverts
      ((CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj) := sorry

/-- The quotient from bounded-below finite filtered homotopy complexes to the corresponding
finite filtered derived category. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
noncomputable def functor :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ Plus.Category C h_inverts :=
  (Plus.property C h_inverts).lift
    ((HomotopyCategory.plus (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- Forgetting the bounded-below target after `functor` recovers the restricted ambient quotient. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
noncomputable def compInclusionIso :
    functor C h_inverts ⋙ (Plus.property C h_inverts).ι ≅
      (HomotopyCategory.plus (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  ObjectProperty.liftCompιIso
    (Plus.property C h_inverts)
    ((HomotopyCategory.plus (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- The kernel of the bounded-below quotient is the bounded-below acyclic property. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
theorem kernel_eq : Functor.kernel (functor C h_inverts) = Plus.Acyclic C := sorry

/-- The bounded-below quotient localizes at bounded-below filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-below finite filtered localization"]
instance isLocalization : Functor.IsLocalization (functor C h_inverts) (Plus.QuasiIso C) := sorry

/-- The canonical bounded-below quotient, using `AssociatedGraded.inverts C` as its certificate.

The certificate-parameterized `functor` remains the underlying construction; this alias is the
default entry point for downstream use. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization"]
noncomputable abbrev canonicalFunctor :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ Plus.canonicalCategory C :=
  functor C (AssociatedGraded.inverts C)

/-- The factorization isomorphism for the canonical bounded-below quotient. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization"]
noncomputable abbrev canonicalCompInclusionIso :
    canonicalFunctor C ⋙ (Plus.canonicalProperty C).ι ≅
      (HomotopyCategory.plus (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  compInclusionIso C (AssociatedGraded.inverts C)

/-- The kernel formula for the canonical bounded-below quotient. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization"]
theorem canonical_kernel_eq :
    Functor.kernel (canonicalFunctor C) = Plus.Acyclic C := sorry

/-- The canonical bounded-below quotient is a localization at filtered quasi-isomorphisms. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization"]
theorem canonical_isLocalization :
    Functor.IsLocalization (canonicalFunctor C) (Plus.QuasiIso C) := sorry

end Plus.Quotient

namespace Minus.Quotient

/-- The ambient finite filtered quotient sends bounded-above complexes to bounded-above objects. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
theorem objMem (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    Minus.property C h_inverts
      ((CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj) := sorry

/-- The quotient from bounded-above finite filtered homotopy complexes to the corresponding
finite filtered derived category. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
noncomputable def functor :
    HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ Minus.Category C h_inverts :=
  (Minus.property C h_inverts).lift
    ((HomotopyCategory.minus (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- Forgetting the bounded-above target after `functor` recovers the restricted ambient quotient. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
noncomputable def compInclusionIso :
    functor C h_inverts ⋙ (Minus.property C h_inverts).ι ≅
      (HomotopyCategory.minus (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  ObjectProperty.liftCompιIso
    (Minus.property C h_inverts)
    ((HomotopyCategory.minus (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- The kernel of the bounded-above quotient is the bounded-above acyclic property. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
theorem kernel_eq : Functor.kernel (functor C h_inverts) = Minus.Acyclic C := sorry

/-- The bounded-above quotient localizes at bounded-above filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-above finite filtered localization"]
instance isLocalization : Functor.IsLocalization (functor C h_inverts) (Minus.QuasiIso C) := sorry

/-- The canonical bounded-above quotient, using `AssociatedGraded.inverts C` as its certificate. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization"]
noncomputable abbrev canonicalFunctor :
    HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ Minus.canonicalCategory C :=
  functor C (AssociatedGraded.inverts C)

/-- The factorization isomorphism for the canonical bounded-above quotient. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization"]
noncomputable abbrev canonicalCompInclusionIso :
    canonicalFunctor C ⋙ (Minus.canonicalProperty C).ι ≅
      (HomotopyCategory.minus (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  compInclusionIso C (AssociatedGraded.inverts C)

/-- The kernel formula for the canonical bounded-above quotient. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization"]
theorem canonical_kernel_eq :
    Functor.kernel (canonicalFunctor C) = Minus.Acyclic C := sorry

/-- The canonical bounded-above quotient is a localization at filtered quasi-isomorphisms. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization"]
theorem canonical_isLocalization :
    Functor.IsLocalization (canonicalFunctor C) (Minus.QuasiIso C) := sorry

end Minus.Quotient

namespace Bounded.Quotient

/-- The ambient finite filtered quotient sends bounded complexes to bounded objects. -/
@[stacks 05S6 "bounded finite filtered localization"]
theorem objMem (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    Bounded.property C h_inverts
      ((CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C).obj X.obj) := sorry

/-- The quotient from bounded finite filtered homotopy complexes to the corresponding finite
filtered derived category. -/
@[stacks 05S6 "bounded finite filtered localization"]
noncomputable def functor :
    HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ Bounded.Category C h_inverts :=
  (Bounded.property C h_inverts).lift
    ((HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- Forgetting the bounded target after `functor` recovers the restricted ambient quotient. -/
@[stacks 05S6 "bounded finite filtered localization"]
noncomputable def compInclusionIso :
    functor C h_inverts ⋙ (Bounded.property C h_inverts).ι ≅
      (HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  ObjectProperty.liftCompιIso
    (Bounded.property C h_inverts)
    ((HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι ⋙
      CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C)
    (objMem C h_inverts)

/-- The kernel of the bounded quotient is the bounded acyclic property. -/
@[stacks 05S6 "bounded finite filtered localization"]
theorem kernel_eq : Functor.kernel (functor C h_inverts) = Bounded.Acyclic C := sorry

/-- The bounded quotient localizes at bounded filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded finite filtered localization"]
instance isLocalization : Functor.IsLocalization (functor C h_inverts) (Bounded.QuasiIso C) := sorry

/-- The canonical bounded quotient, using `AssociatedGraded.inverts C` as its certificate. -/
@[stacks 05S6 "canonical finite filtered localization"]
noncomputable abbrev canonicalFunctor :
    HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ Bounded.canonicalCategory C :=
  functor C (AssociatedGraded.inverts C)

/-- The factorization isomorphism for the canonical bounded quotient. -/
@[stacks 05S6 "canonical finite filtered localization"]
noncomputable abbrev canonicalCompInclusionIso :
    canonicalFunctor C ⋙ (Bounded.canonicalProperty C).ι ≅
      (HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι ⋙
        CategoryTheory.FilteredObject.FiniteDerived.Quotient.functor C :=
  compInclusionIso C (AssociatedGraded.inverts C)

/-- The kernel formula for the canonical bounded quotient. -/
@[stacks 05S6 "canonical finite filtered localization"]
theorem canonical_kernel_eq :
    Functor.kernel (canonicalFunctor C) = Bounded.Acyclic C := sorry

/-- The canonical bounded quotient is a localization at filtered quasi-isomorphisms. -/
@[stacks 05S6 "canonical finite filtered localization"]
theorem canonical_isLocalization :
    Functor.IsLocalization (canonicalFunctor C) (Bounded.QuasiIso C) := sorry

end Bounded.Quotient

end CategoryTheory.FilteredObject.FiniteDerived
