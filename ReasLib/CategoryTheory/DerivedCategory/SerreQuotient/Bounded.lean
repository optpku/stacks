/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.SerreQuotient
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded

/-!
# Bounded Derived Serre Quotients

This file restricts the derived functor of a Serre quotient to the bounded-below,
bounded-above, and bounded derived categories.  Each restriction is exposed together with its
comparison to the ambient derived functor, its kernel, and its localization interface.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe wA wQ vA uA

namespace CategoryTheory.ObjectProperty.SerreClassLocalization.Derived

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wQ} P.isoModSerre.Localization]

namespace Plus.Quotient

/-- The derived Serre quotient sends bounded-below objects to bounded-below objects. -/
theorem obj_mem (X : DerivedCategory.Plus A) :
    (t.plus : ObjectProperty (DerivedCategory P.isoModSerre.Localization))
      ((DerivedCategory.Plus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory).obj X) := sorry

/-- The restriction of the derived Serre quotient functor to bounded-below derived
categories. -/
@[stacks 06XM "bounded-below derived Serre quotient"]
noncomputable def functor :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus P.isoModSerre.Localization :=
  (t.plus : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).lift
    (DerivedCategory.Plus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- Forgetting the bounded-below restriction recovers the ambient derived Serre quotient
functor on bounded-below objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory :=
  (t.plus : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).liftCompιIso
    (DerivedCategory.Plus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- The kernel of the bounded-below derived Serre quotient is the property of having
cohomology in the Serre class. -/
@[stacks 06XM "bounded-below derived Serre kernel"]
theorem kernel_eq :
    Functor.kernel (functor P) = DerivedCategory.Plus.cohomologyIn P := sorry

/-- Stacks 06XM (bounded-below): a Serre quotient with a fully faithful left adjoint induces
the localization of the bounded-below derived category at the cohomology-in-`P` Verdier system. -/
@[stacks 06XM "bounded-below derived Serre localization"]
theorem isLocalization
    (u : P.isoModSerre.Localization ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q) [u.Full] [u.Faithful] :
    (functor P).IsLocalization (DerivedCategory.Plus.cohomologyIn P).trW := sorry

end Plus.Quotient

namespace Minus.Quotient

/-- The derived Serre quotient sends bounded-above objects to bounded-above objects. -/
theorem obj_mem (X : DerivedCategory.Minus A) :
    (t.minus : ObjectProperty (DerivedCategory P.isoModSerre.Localization))
      ((DerivedCategory.Minus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory).obj X) := sorry

/-- The restriction of the derived Serre quotient functor to bounded-above derived
categories. -/
@[stacks 06XM "bounded-above derived Serre quotient"]
noncomputable def functor :
    DerivedCategory.Minus A ⥤ DerivedCategory.Minus P.isoModSerre.Localization :=
  (t.minus : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).lift
    (DerivedCategory.Minus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- Forgetting the bounded-above restriction recovers the ambient derived Serre quotient
functor on bounded-above objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory :=
  (t.minus : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).liftCompιIso
    (DerivedCategory.Minus.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- The kernel of the bounded-above derived Serre quotient is the property of having
cohomology in the Serre class. -/
@[stacks 06XM "bounded-above derived Serre kernel"]
theorem kernel_eq :
    Functor.kernel (functor P) = DerivedCategory.Minus.cohomologyIn P := sorry

/-- Stacks 06XM (bounded-above): a Serre quotient with a fully faithful left adjoint induces
the localization of the bounded-above derived category at the cohomology-in-`P` Verdier system. -/
@[stacks 06XM "bounded-above derived Serre localization"]
theorem isLocalization
    (u : P.isoModSerre.Localization ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q) [u.Full] [u.Faithful] :
    (functor P).IsLocalization (DerivedCategory.Minus.cohomologyIn P).trW := sorry

end Minus.Quotient

namespace Bounded.Quotient

/-- The derived Serre quotient sends bounded objects to bounded objects. -/
theorem obj_mem (X : DerivedCategory.Bounded A) :
    (t.bounded : ObjectProperty (DerivedCategory P.isoModSerre.Localization))
      ((DerivedCategory.Bounded.ι ⋙ P.isoModSerre.Q.mapDerivedCategory).obj X) := sorry

/-- The restriction of the derived Serre quotient functor to bounded derived categories. -/
@[stacks 06XM "bounded derived Serre quotient"]
noncomputable def functor :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded P.isoModSerre.Localization :=
  (t.bounded : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).lift
    (DerivedCategory.Bounded.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- Forgetting the bounded restriction recovers the ambient derived Serre quotient functor on
bounded objects. -/
noncomputable def compιIso :
    functor P ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ P.isoModSerre.Q.mapDerivedCategory :=
  (t.bounded : ObjectProperty (DerivedCategory P.isoModSerre.Localization)).liftCompιIso
    (DerivedCategory.Bounded.ι ⋙ P.isoModSerre.Q.mapDerivedCategory) (obj_mem P)

/-- The kernel of the bounded derived Serre quotient is the property of having cohomology in
the Serre class. -/
@[stacks 06XM "bounded derived Serre kernel"]
theorem kernel_eq :
    Functor.kernel (functor P) = DerivedCategory.Bounded.cohomologyIn P := sorry

/-- Stacks 06XM (bounded): a Serre quotient with a fully faithful left adjoint induces the
localization of the bounded derived category at the cohomology-in-`P` Verdier system. -/
@[stacks 06XM "bounded derived Serre localization"]
theorem isLocalization
    (u : P.isoModSerre.Localization ⥤ A)
    (adj : u ⊣ P.isoModSerre.Q) [u.Full] [u.Faithful] :
    (functor P).IsLocalization (DerivedCategory.Bounded.cohomologyIn P).trW := sorry

end Bounded.Quotient

end CategoryTheory.ObjectProperty.SerreClassLocalization.Derived
