/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact bounded-below finite filtered derived functors

This leaf registers the shift and exactness structures of the bounded-below graded-piece and
forgetful homotopy functors and transports them through their explicit localization lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.GradedPiece.Homotopy

/-- The bounded-below graded-piece homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) :
    (Plus.GradedPiece.homotopy C p).CommShift ℤ :=
  inferInstanceAs
    ((((FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).CommShift ℤ)

/-- The bounded-below graded-piece homotopy functor is exact. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) :
    (Plus.GradedPiece.homotopy C p).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).IsTriangulated)

end Plus.GradedPiece.Homotopy

namespace Plus.GradedPiece.Lift

/-- A bounded-below derived graded-piece lift commutes with integer shifts. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) (h_piece : Plus.GradedPiece.Inverts C p) :
    (Plus.GradedPiece.lift C h_inverts p h_piece).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Plus.QuasiIso C) (Plus.Quotient.functor C h_inverts)
    (Plus.GradedPiece.homotopy C p) h_piece

/-- A bounded-below derived graded-piece lift is exact. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) (h_piece : Plus.GradedPiece.Inverts C p) :
    (Plus.GradedPiece.lift C h_inverts p h_piece).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Plus.QuasiIso C) (Plus.Quotient.functor C h_inverts)
    (Plus.GradedPiece.homotopy C p) h_piece

end Plus.GradedPiece.Lift

namespace Plus.Forget.Homotopy

/-- The bounded-below forgetful homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
noncomputable instance commShift : (Plus.Forget.homotopy C).CommShift ℤ :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).CommShift ℤ)

/-- The bounded-below forgetful homotopy functor is exact. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
instance isTriangulated : (Plus.Forget.homotopy C).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).IsTriangulated)

end Plus.Forget.Homotopy

namespace Plus.Forget.Lift

/-- A bounded-below derived forgetful lift commutes with integer shifts. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
noncomputable instance commShift (h_forget : Plus.Forget.Inverts C) :
    (Plus.Forget.lift C h_inverts h_forget).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Plus.QuasiIso C) (Plus.Quotient.functor C h_inverts)
    (Plus.Forget.homotopy C) h_forget

/-- A bounded-below derived forgetful lift is exact. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
instance isTriangulated (h_forget : Plus.Forget.Inverts C) :
    (Plus.Forget.lift C h_inverts h_forget).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Plus.QuasiIso C) (Plus.Quotient.functor C h_inverts)
    (Plus.Forget.homotopy C) h_forget

end Plus.Forget.Lift

end CategoryTheory.FilteredObject.FiniteDerived
