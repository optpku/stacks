/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Left-derived comparisons for bounded-above finite filtered functors

This is the bounded-above dual of the `Plus` right-derived comparison API.  It specializes
Mathlib's uniqueness theorem for left derived functors to the graded-piece and forgetful lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.FilteredObject.FiniteDerived

variable {A : Type uA} [_root_.CategoryTheory.Category.{vA} A] [Abelian A]
variable {B : Type uB} [_root_.CategoryTheory.Category.{vB} B] [Abelian B]
variable [HasDerivedCategory A] [HasDerivedCategory B]
variable [HasDerivedCategory (GradedObject ℤ A)] [HasDerivedCategory (GradedObject ℤ B)]
variable (hA : AssociatedGraded.Inverts A)
  (hB : AssociatedGraded.Inverts B)

namespace Minus.GradedPiece.LeftDerived

/-- The canonical comparison between taking a graded piece after a bounded-above left-derived
filtered functor and left-deriving the corresponding graded-piece functor. -/
@[stacks 05S6 "bounded-above filtered derived graded-piece comparison"]
noncomputable def iso (p : ℤ)
    (h_pieceA : Inverts A p) (h_pieceB : Inverts B p)
    (source : HomotopyCategory.Minus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Minus B)
    (filtered : Minus.Category A hA ⥤ Minus.Category B hB)
    (ordinary : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
    (α : Minus.Quotient.functor A hA ⋙ (filtered ⋙ lift B hB p h_pieceB) ⟶ source)
    (β : Minus.Quotient.functor A hA ⋙ (lift A hA p h_pieceA ⋙ ordinary) ⟶ source)
    [Functor.IsLeftDerivedFunctor
      (filtered ⋙ lift B hB p h_pieceB) α (Minus.QuasiIso A)]
    [Functor.IsLeftDerivedFunctor
      (lift A hA p h_pieceA ⋙ ordinary) β (Minus.QuasiIso A)] :
    filtered ⋙ lift B hB p h_pieceB ≅ lift A hA p h_pieceA ⋙ ordinary :=
  (lift A hA p h_pieceA ⋙ ordinary).leftDerivedUnique
    (filtered ⋙ lift B hB p h_pieceB) α β (Minus.QuasiIso A)

section Computation

variable (p : ℤ) (h_pieceA : Inverts A p) (h_pieceB : Inverts B p)
variable (source : HomotopyCategory.Minus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Minus B)
variable (filtered : Minus.Category A hA ⥤ Minus.Category B hB)
variable (ordinary : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
variable (α : Minus.Quotient.functor A hA ⋙
  (filtered ⋙ lift B hB p h_pieceB) ⟶ source)
variable (β : Minus.Quotient.functor A hA ⋙
  (lift A hA p h_pieceA ⋙ ordinary) ⟶ source)
variable [Functor.IsLeftDerivedFunctor
  (filtered ⋙ lift B hB p h_pieceB) α (Minus.QuasiIso A)]
variable [Functor.IsLeftDerivedFunctor
  (lift A hA p h_pieceA ⋙ ordinary) β (Minus.QuasiIso A)]

/-- The comparison `iso` carries the first left-derived factorization to the second. -/
@[reassoc (attr := simp), stacks 05S6 "left-derived factorization"]
theorem fac :
    Functor.whiskerLeft (Minus.Quotient.functor A hA)
        (iso hA hB p h_pieceA h_pieceB source filtered ordinary α β).hom ≫ β = α := sorry

/-- Componentwise form of `LeftDerived.fac`. -/
@[simp, stacks 05S6 "left-derived factorization"]
theorem fac_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category A)) :
    (iso hA hB p h_pieceA h_pieceB source filtered ordinary α β).hom.app
          ((Minus.Quotient.functor A hA).obj X) ≫ β.app X = α.app X := sorry

/-- The inverse comparison carries the second left-derived factorization back to the first. -/
@[reassoc (attr := simp), stacks 05S6 "left-derived inverse factorization"]
theorem inv_fac :
    Functor.whiskerLeft (Minus.Quotient.functor A hA)
        (iso hA hB p h_pieceA h_pieceB source filtered ordinary α β).inv ≫ α = β := sorry

/-- Componentwise form of `LeftDerived.inv_fac`. -/
@[simp, stacks 05S6 "left-derived inverse factorization"]
theorem inv_fac_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category A)) :
    (iso hA hB p h_pieceA h_pieceB source filtered ordinary α β).inv.app
          ((Minus.Quotient.functor A hA).obj X) ≫ α.app X = β.app X := sorry

end Computation

end Minus.GradedPiece.LeftDerived

namespace Minus.Forget.LeftDerived

/-- The canonical comparison between forgetting after a bounded-above left-derived filtered
functor and left-deriving the corresponding unfiltered functor. -/
@[stacks 05S6 "bounded-above filtered derived forgetful comparison"]
noncomputable def iso
    (h_forgetA : Inverts A) (h_forgetB : Inverts B)
    (source : HomotopyCategory.Minus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Minus B)
    (filtered : Minus.Category A hA ⥤ Minus.Category B hB)
    (ordinary : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
    (α : Minus.Quotient.functor A hA ⋙ (filtered ⋙ lift B hB h_forgetB) ⟶ source)
    (β : Minus.Quotient.functor A hA ⋙ (lift A hA h_forgetA ⋙ ordinary) ⟶ source)
    [Functor.IsLeftDerivedFunctor
      (filtered ⋙ lift B hB h_forgetB) α (Minus.QuasiIso A)]
    [Functor.IsLeftDerivedFunctor
      (lift A hA h_forgetA ⋙ ordinary) β (Minus.QuasiIso A)] :
    filtered ⋙ lift B hB h_forgetB ≅ lift A hA h_forgetA ⋙ ordinary :=
  (lift A hA h_forgetA ⋙ ordinary).leftDerivedUnique
    (filtered ⋙ lift B hB h_forgetB) α β (Minus.QuasiIso A)

section Computation

variable (h_forgetA : Inverts A) (h_forgetB : Inverts B)
variable (source : HomotopyCategory.Minus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Minus B)
variable (filtered : Minus.Category A hA ⥤ Minus.Category B hB)
variable (ordinary : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B)
variable (α : Minus.Quotient.functor A hA ⋙
  (filtered ⋙ lift B hB h_forgetB) ⟶ source)
variable (β : Minus.Quotient.functor A hA ⋙
  (lift A hA h_forgetA ⋙ ordinary) ⟶ source)
variable [Functor.IsLeftDerivedFunctor
  (filtered ⋙ lift B hB h_forgetB) α (Minus.QuasiIso A)]
variable [Functor.IsLeftDerivedFunctor
  (lift A hA h_forgetA ⋙ ordinary) β (Minus.QuasiIso A)]

/-- The forgetful comparison carries the first left-derived factorization to the second. -/
@[reassoc (attr := simp), stacks 05S6 "left-derived factorization"]
theorem fac :
    Functor.whiskerLeft (Minus.Quotient.functor A hA)
        (iso hA hB h_forgetA h_forgetB source filtered ordinary α β).hom ≫ β = α := sorry

/-- Componentwise form of `LeftDerived.fac` for forgetting filtrations. -/
@[simp, stacks 05S6 "left-derived factorization"]
theorem fac_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category A)) :
    (iso hA hB h_forgetA h_forgetB source filtered ordinary α β).hom.app
          ((Minus.Quotient.functor A hA).obj X) ≫ β.app X = α.app X := sorry

/-- The inverse forgetful comparison carries the second factorization back to the first. -/
@[reassoc (attr := simp), stacks 05S6 "left-derived inverse factorization"]
theorem inv_fac :
    Functor.whiskerLeft (Minus.Quotient.functor A hA)
        (iso hA hB h_forgetA h_forgetB source filtered ordinary α β).inv ≫ α = β := sorry

/-- Componentwise form of `LeftDerived.inv_fac` for forgetting filtrations. -/
@[simp, stacks 05S6 "left-derived inverse factorization"]
theorem inv_fac_app (X : HomotopyCategory.Minus (FilteredObject.Finite.category A)) :
    (iso hA hB h_forgetA h_forgetB source filtered ordinary α β).inv.app
          ((Minus.Quotient.functor A hA).obj X) ≫ α.app X = β.app X := sorry

end Computation

end Minus.Forget.LeftDerived

end CategoryTheory.FilteredObject.FiniteDerived
