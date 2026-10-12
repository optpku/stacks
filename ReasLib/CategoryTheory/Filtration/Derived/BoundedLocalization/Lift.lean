/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal lifts from bounded finite filtered homotopy categories

For each boundedness convention, this leaf exposes the localization lift and its factorization
isomorphism under the same `Quotient` namespace as the corresponding quotient functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.Quotient

/-- The universal lift of a functor from bounded-below finite filtered homotopy complexes that
inverts bounded-below filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-below finite filtered localization lift"]
noncomputable def lift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Plus.QuasiIso C).IsInvertedBy F) : Plus.Category C h_inverts ⥤ D :=
  CategoryTheory.Localization.lift F hF (functor C h_inverts)

/-- The universal factorization isomorphism for `lift`. -/
@[stacks 05S6 "bounded-below finite filtered localization lift"]
noncomputable def facIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Plus.QuasiIso C).IsInvertedBy F) :
    functor C h_inverts ⋙ lift C h_inverts F hF ≅ F :=
  CategoryTheory.Localization.fac F hF (functor C h_inverts)

/-- The canonical bounded-below localization lift, using `AssociatedGraded.inverts C`. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization lift"]
noncomputable abbrev canonicalLift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Plus.QuasiIso C).IsInvertedBy F) : Plus.canonicalCategory C ⥤ D :=
  lift C (AssociatedGraded.inverts C) F hF

/-- The universal factorization isomorphism for `canonicalLift`. -/
@[stacks 05S6 "canonical bounded-below finite filtered localization lift"]
noncomputable abbrev canonicalFacIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Plus.QuasiIso C).IsInvertedBy F) :
    Plus.Quotient.canonicalFunctor C ⋙ canonicalLift C F hF ≅ F :=
  facIso C (AssociatedGraded.inverts C) F hF

end Plus.Quotient

namespace Minus.Quotient

/-- The universal lift of a functor from bounded-above finite filtered homotopy complexes that
inverts bounded-above filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-above finite filtered localization lift"]
noncomputable def lift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Minus.QuasiIso C).IsInvertedBy F) : Minus.Category C h_inverts ⥤ D :=
  CategoryTheory.Localization.lift F hF (functor C h_inverts)

/-- The universal factorization isomorphism for `lift`. -/
@[stacks 05S6 "bounded-above finite filtered localization lift"]
noncomputable def facIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Minus.QuasiIso C).IsInvertedBy F) :
    functor C h_inverts ⋙ lift C h_inverts F hF ≅ F :=
  CategoryTheory.Localization.fac F hF (functor C h_inverts)

/-- The canonical bounded-above localization lift, using `AssociatedGraded.inverts C`. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization lift"]
noncomputable abbrev canonicalLift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Minus.QuasiIso C).IsInvertedBy F) : Minus.canonicalCategory C ⥤ D :=
  lift C (AssociatedGraded.inverts C) F hF

/-- The universal factorization isomorphism for the canonical bounded-above lift. -/
@[stacks 05S6 "canonical bounded-above finite filtered localization lift"]
noncomputable abbrev canonicalFacIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Minus.QuasiIso C).IsInvertedBy F) :
    Minus.Quotient.canonicalFunctor C ⋙ canonicalLift C F hF ≅ F :=
  facIso C (AssociatedGraded.inverts C) F hF

end Minus.Quotient

namespace Bounded.Quotient

/-- The universal lift of a functor from bounded finite filtered homotopy complexes that inverts
bounded filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded finite filtered localization lift"]
noncomputable def lift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Bounded.QuasiIso C).IsInvertedBy F) : Bounded.Category C h_inverts ⥤ D :=
  CategoryTheory.Localization.lift F hF (functor C h_inverts)

/-- The universal factorization isomorphism for `lift`. -/
@[stacks 05S6 "bounded finite filtered localization lift"]
noncomputable def facIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Bounded.QuasiIso C).IsInvertedBy F) :
    functor C h_inverts ⋙ lift C h_inverts F hF ≅ F :=
  CategoryTheory.Localization.fac F hF (functor C h_inverts)

/-- The canonical bounded localization lift, using `AssociatedGraded.inverts C`. -/
@[stacks 05S6 "canonical finite filtered localization lift"]
noncomputable abbrev canonicalLift {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Bounded.QuasiIso C).IsInvertedBy F) : Bounded.canonicalCategory C ⥤ D :=
  lift C (AssociatedGraded.inverts C) F hF

/-- The universal factorization isomorphism for the canonical bounded lift. -/
@[stacks 05S6 "canonical finite filtered localization lift"]
noncomputable abbrev canonicalFacIso {D : Type*} [_root_.CategoryTheory.Category D]
    (F : HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ D)
    (hF : (Bounded.QuasiIso C).IsInvertedBy F) :
    Bounded.Quotient.canonicalFunctor C ⋙ canonicalLift C F hF ≅ F :=
  facIso C (AssociatedGraded.inverts C) F hF

end Bounded.Quotient

end CategoryTheory.FilteredObject.FiniteDerived
