module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-derived comparisons for bounded-below finite filtered functors

These comparison isomorphisms are thin specializations of Mathlib's uniqueness theorem for right
derived functors.  They live in a separate leaf because the graded-piece and forgetful localization
lifts themselves do not depend on Kan-extension infrastructure.
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

namespace Plus.GradedPiece.RightDerived

/-- The canonical comparison between taking a graded piece after a bounded-below right-derived
filtered functor and right-deriving the corresponding graded-piece functor. -/
noncomputable def iso (p : ℤ)
    (h_pieceA : Inverts A p) (h_pieceB : Inverts B p)
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
    {filtered : Plus.Category A hA ⥤ Plus.Category B hB}
    {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (α : source ⟶ Plus.Quotient.functor A hA ⋙ (filtered ⋙ lift B hB p h_pieceB))
    (β : source ⟶ Plus.Quotient.functor A hA ⋙ (lift A hA p h_pieceA ⋙ ordinary))
    [Functor.IsRightDerivedFunctor
      (filtered ⋙ lift B hB p h_pieceB) α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      (lift A hA p h_pieceA ⋙ ordinary) β (Plus.QuasiIso A)] :
    filtered ⋙ lift B hB p h_pieceB ≅ lift A hA p h_pieceA ⋙ ordinary :=
  (filtered ⋙ lift B hB p h_pieceB).rightDerivedUnique
    (lift A hA p h_pieceA ⋙ ordinary) α β (Plus.QuasiIso A)

/-- The proof-stable graded-piece comparison for the canonical bounded-below finite filtered
derived categories.

The source and the two candidate derived functors are inferred from `α` and `β`; the canonical
localization and graded-piece inversion certificates remain internal to the library. -/
noncomputable def canonicalIso (p : ℤ)
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
    {filtered : Plus.canonicalCategory A ⥤ Plus.canonicalCategory B}
    {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (α : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
      (filtered ⋙ Plus.GradedPiece.canonicalLift B p))
    (β : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
      (Plus.GradedPiece.canonicalLift A p ⋙ ordinary))
    [Functor.IsRightDerivedFunctor
      (filtered ⋙ Plus.GradedPiece.canonicalLift B p) α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      (Plus.GradedPiece.canonicalLift A p ⋙ ordinary) β (Plus.QuasiIso A)] :
    filtered ⋙ Plus.GradedPiece.canonicalLift B p ≅
      Plus.GradedPiece.canonicalLift A p ⋙ ordinary :=
  (filtered ⋙ Plus.GradedPiece.canonicalLift B p).rightDerivedUnique
    (Plus.GradedPiece.canonicalLift A p ⋙ ordinary) α β (Plus.QuasiIso A)

namespace canonicalIso

variable (p : ℤ)
variable {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤
  DerivedCategory.Plus B}
variable {filtered : Plus.canonicalCategory A ⥤ Plus.canonicalCategory B}
variable {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable (α : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
  (filtered ⋙ Plus.GradedPiece.canonicalLift B p))
variable (β : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
  (Plus.GradedPiece.canonicalLift A p ⋙ ordinary))
variable [Functor.IsRightDerivedFunctor
  (filtered ⋙ Plus.GradedPiece.canonicalLift B p) α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  (Plus.GradedPiece.canonicalLift A p ⋙ ordinary) β (Plus.QuasiIso A)]

/-- The canonical graded-piece comparison carries the first right-derived factorization to the
second. -/
@[reassoc (attr := simp)]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A)
        (canonicalIso p α β).hom = β := sorry

/-- Componentwise form of `canonicalIso.fac`. -/
@[simp]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (canonicalIso p α β).hom.app
          ((Plus.Quotient.canonicalFunctor A).obj X) = β.app X := sorry

/-- The inverse canonical graded-piece comparison carries the second right-derived factorization
back to the first. -/
@[reassoc (attr := simp)]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A)
        (canonicalIso p α β).inv = α := sorry

/-- Componentwise form of `canonicalIso.inv_fac`. -/
@[simp]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (canonicalIso p α β).inv.app
          ((Plus.Quotient.canonicalFunctor A).obj X) = α.app X := sorry

end canonicalIso

section Computation

variable (p : ℤ) (h_pieceA : Inverts A p) (h_pieceB : Inverts B p)
variable {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
variable {filtered : Plus.Category A hA ⥤ Plus.Category B hB}
variable {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable (α : source ⟶ Plus.Quotient.functor A hA ⋙
  (filtered ⋙ lift B hB p h_pieceB))
variable (β : source ⟶ Plus.Quotient.functor A hA ⋙
  (lift A hA p h_pieceA ⋙ ordinary))
variable [Functor.IsRightDerivedFunctor
  (filtered ⋙ lift B hB p h_pieceB) α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  (lift A hA p h_pieceA ⋙ ordinary) β (Plus.QuasiIso A)]

/-- The comparison `iso` carries the first right-derived factorization to the second. -/
@[reassoc (attr := simp)]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA hB p h_pieceA h_pieceB α β).hom = β := sorry

/-- Componentwise form of `RightDerived.fac`. -/
@[simp]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (iso hA hB p h_pieceA h_pieceB α β).hom.app
          ((Plus.Quotient.functor A hA).obj X) = β.app X := sorry

/-- The inverse comparison carries the second right-derived factorization back to the first. -/
@[reassoc (attr := simp)]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA hB p h_pieceA h_pieceB α β).inv = α := sorry

/-- Componentwise form of `RightDerived.inv_fac`. -/
@[simp]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (iso hA hB p h_pieceA h_pieceB α β).inv.app
          ((Plus.Quotient.functor A hA).obj X) = α.app X := sorry

end Computation

end Plus.GradedPiece.RightDerived

namespace Plus.Forget.RightDerived

/-- The canonical comparison between forgetting after a bounded-below right-derived filtered
functor and right-deriving the corresponding unfiltered functor. -/
noncomputable def iso
    (h_forgetA : Inverts A) (h_forgetB : Inverts B)
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
    {filtered : Plus.Category A hA ⥤ Plus.Category B hB}
    {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (α : source ⟶ Plus.Quotient.functor A hA ⋙ (filtered ⋙ lift B hB h_forgetB))
    (β : source ⟶ Plus.Quotient.functor A hA ⋙ (lift A hA h_forgetA ⋙ ordinary))
    [Functor.IsRightDerivedFunctor
      (filtered ⋙ lift B hB h_forgetB) α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      (lift A hA h_forgetA ⋙ ordinary) β (Plus.QuasiIso A)] :
    filtered ⋙ lift B hB h_forgetB ≅ lift A hA h_forgetA ⋙ ordinary :=
  (filtered ⋙ lift B hB h_forgetB).rightDerivedUnique
    (lift A hA h_forgetA ⋙ ordinary) α β (Plus.QuasiIso A)

/-- The proof-stable forgetful comparison for the canonical bounded-below finite filtered derived
categories.

The source and the two candidate derived functors are inferred from `α` and `β`; the canonical
localization and forgetful inversion certificates remain internal to the library. -/
noncomputable def canonicalIso
    {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
    {filtered : Plus.canonicalCategory A ⥤ Plus.canonicalCategory B}
    {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (α : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
      (filtered ⋙ Plus.Forget.canonicalLift B))
    (β : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
      (Plus.Forget.canonicalLift A ⋙ ordinary))
    [Functor.IsRightDerivedFunctor
      (filtered ⋙ Plus.Forget.canonicalLift B) α (Plus.QuasiIso A)]
    [Functor.IsRightDerivedFunctor
      (Plus.Forget.canonicalLift A ⋙ ordinary) β (Plus.QuasiIso A)] :
    filtered ⋙ Plus.Forget.canonicalLift B ≅
      Plus.Forget.canonicalLift A ⋙ ordinary :=
  (filtered ⋙ Plus.Forget.canonicalLift B).rightDerivedUnique
    (Plus.Forget.canonicalLift A ⋙ ordinary) α β (Plus.QuasiIso A)

namespace canonicalIso

variable {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤
  DerivedCategory.Plus B}
variable {filtered : Plus.canonicalCategory A ⥤ Plus.canonicalCategory B}
variable {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable (α : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
  (filtered ⋙ Plus.Forget.canonicalLift B))
variable (β : source ⟶ Plus.Quotient.canonicalFunctor A ⋙
  (Plus.Forget.canonicalLift A ⋙ ordinary))
variable [Functor.IsRightDerivedFunctor
  (filtered ⋙ Plus.Forget.canonicalLift B) α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  (Plus.Forget.canonicalLift A ⋙ ordinary) β (Plus.QuasiIso A)]

/-- The canonical forgetful comparison carries the first right-derived factorization to the
second. -/
@[reassoc (attr := simp)]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A)
        (canonicalIso α β).hom = β := sorry

/-- Componentwise form of `canonicalIso.fac`. -/
@[simp]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (canonicalIso α β).hom.app
          ((Plus.Quotient.canonicalFunctor A).obj X) = β.app X := sorry

/-- The inverse canonical forgetful comparison carries the second right-derived factorization
back to the first. -/
@[reassoc (attr := simp)]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.canonicalFunctor A)
        (canonicalIso α β).inv = α := sorry

/-- Componentwise form of `canonicalIso.inv_fac`. -/
@[simp]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (canonicalIso α β).inv.app
          ((Plus.Quotient.canonicalFunctor A).obj X) = α.app X := sorry

end canonicalIso

section Computation

variable (h_forgetA : Inverts A) (h_forgetB : Inverts B)
variable {source : HomotopyCategory.Plus (FilteredObject.Finite.category A) ⥤ DerivedCategory.Plus B}
variable {filtered : Plus.Category A hA ⥤ Plus.Category B hB}
variable {ordinary : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
variable (α : source ⟶ Plus.Quotient.functor A hA ⋙
  (filtered ⋙ lift B hB h_forgetB))
variable (β : source ⟶ Plus.Quotient.functor A hA ⋙
  (lift A hA h_forgetA ⋙ ordinary))
variable [Functor.IsRightDerivedFunctor
  (filtered ⋙ lift B hB h_forgetB) α (Plus.QuasiIso A)]
variable [Functor.IsRightDerivedFunctor
  (lift A hA h_forgetA ⋙ ordinary) β (Plus.QuasiIso A)]

/-- The forgetful comparison carries the first right-derived factorization to the second. -/
@[reassoc (attr := simp)]
theorem fac :
    α ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA hB h_forgetA h_forgetB α β).hom = β := sorry

/-- Componentwise form of `RightDerived.fac` for forgetting filtrations. -/
@[simp]
theorem fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    α.app X ≫
        (iso hA hB h_forgetA h_forgetB α β).hom.app
          ((Plus.Quotient.functor A hA).obj X) = β.app X := sorry

/-- The inverse forgetful comparison carries the second factorization back to the first. -/
@[reassoc (attr := simp)]
theorem inv_fac :
    β ≫ Functor.whiskerLeft (Plus.Quotient.functor A hA)
        (iso hA hB h_forgetA h_forgetB α β).inv = α := sorry

/-- Componentwise form of `RightDerived.inv_fac` for forgetting filtrations. -/
@[simp]
theorem inv_fac_app (X : HomotopyCategory.Plus (FilteredObject.Finite.category A)) :
    β.app X ≫
        (iso hA hB h_forgetA h_forgetB α β).inv.app
          ((Plus.Quotient.functor A hA).obj X) = α.app X := sorry

end Computation

end Plus.Forget.RightDerived

end CategoryTheory.FilteredObject.FiniteDerived
