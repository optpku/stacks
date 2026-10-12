/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.SerreClassLocalization
open CategoryTheory.Equivalence.MapDerivedCategory
open ExactFunctor.Derived

noncomputable section

universe wA wQ wB vA vB uA uB

namespace CategoryTheory.ObjectProperty.SerreClassLocalization.Derived

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} P.isoModSerre.Localization]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory.{wB} B]

namespace Quotient

/-- A derived Serre quotient followed by an equivalence is a localization when the composite
admits an explicit left adjoint with invertible unit. -/
theorem isLocalization_comp_equivalence_of_adjunction
    (e : P.isoModSerre.Localization ≌ B) (u : B ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q ⋙ e.functor) [h_unit : IsIso adj.unit] :
    (P.isoModSerre.Q.mapDerivedCategory ⋙ functor e).IsLocalization
      (DerivedCategory.cohomologyIn P).trW := sorry

/-- A derived Serre quotient followed by an explicit equivalence of its target is a localization
at complexes whose cohomology belongs to the Serre class. -/
noncomputable instance isLocalization_comp_equivalence (e :
    P.isoModSerre.Localization ≌ B)
    [P.isoModSerre.Q.IsRightAdjoint]
    [(Functor.leftAdjoint P.isoModSerre.Q).Full]
    [(Functor.leftAdjoint P.isoModSerre.Q).Faithful] :
    (P.isoModSerre.Q.mapDerivedCategory ⋙ functor e).IsLocalization
      (DerivedCategory.cohomologyIn P).trW := sorry

end Quotient

namespace Plus.Quotient

/-- The bounded-below derived Serre quotient followed by an equivalence is a localization when
the composite admits an explicit left adjoint with invertible unit. -/
theorem isLocalization_comp_equivalence_of_adjunction
    (e : P.isoModSerre.Localization ≌ B) (u : B ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q ⋙ e.functor) [h_unit : IsIso adj.unit] :
    (Plus.Quotient.functor P ⋙
      Plus.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Plus.cohomologyIn P).trW := sorry

/-- The bounded-below restriction of a derived Serre quotient remains a localization after
postcomposition with an explicit equivalence of abelian targets. -/
noncomputable instance isLocalization_comp_equivalence (e :
    P.isoModSerre.Localization ≌ B)
    [P.isoModSerre.Q.IsRightAdjoint]
    [(Functor.leftAdjoint P.isoModSerre.Q).Full]
    [(Functor.leftAdjoint P.isoModSerre.Q).Faithful] :
    (Plus.Quotient.functor P ⋙
      Plus.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Plus.cohomologyIn P).trW := sorry

end Plus.Quotient

namespace Minus.Quotient

/-- The bounded-above derived Serre quotient followed by an equivalence is a localization when
the composite admits an explicit left adjoint with invertible unit. -/
theorem isLocalization_comp_equivalence_of_adjunction
    (e : P.isoModSerre.Localization ≌ B) (u : B ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q ⋙ e.functor) [h_unit : IsIso adj.unit] :
    (Minus.Quotient.functor P ⋙
      Minus.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Minus.cohomologyIn P).trW := sorry

/-- The bounded-above restriction of a derived Serre quotient remains a localization after
postcomposition with an explicit equivalence of abelian targets. -/
noncomputable instance isLocalization_comp_equivalence (e :
    P.isoModSerre.Localization ≌ B)
    [P.isoModSerre.Q.IsRightAdjoint]
    [(Functor.leftAdjoint P.isoModSerre.Q).Full]
    [(Functor.leftAdjoint P.isoModSerre.Q).Faithful] :
    (Minus.Quotient.functor P ⋙
      Minus.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Minus.cohomologyIn P).trW := sorry

end Minus.Quotient

namespace Bounded.Quotient

/-- The bounded derived Serre quotient followed by an equivalence is a localization when the
composite admits an explicit left adjoint with invertible unit. -/
theorem isLocalization_comp_equivalence_of_adjunction
    (e : P.isoModSerre.Localization ≌ B) (u : B ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q ⋙ e.functor) [h_unit : IsIso adj.unit] :
    (Bounded.Quotient.functor P ⋙
      Bounded.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Bounded.cohomologyIn P).trW := sorry

/-- The bounded restriction of a derived Serre quotient remains a localization after
postcomposition with an explicit equivalence of abelian targets. -/
noncomputable instance isLocalization_comp_equivalence (e :
    P.isoModSerre.Localization ≌ B)
    [P.isoModSerre.Q.IsRightAdjoint]
    [(Functor.leftAdjoint P.isoModSerre.Q).Full]
    [(Functor.leftAdjoint P.isoModSerre.Q).Faithful] :
    (Bounded.Quotient.functor P ⋙
      Bounded.functor (forwardExact e)).IsLocalization
        (DerivedCategory.Bounded.cohomologyIn P).trW := sorry

end Bounded.Quotient

end CategoryTheory.ObjectProperty.SerreClassLocalization.Derived
