/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact bounded-above finite filtered derived functors

This leaf registers the shift and exactness structures of the bounded-above graded-piece and
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

namespace Minus.GradedPiece.Homotopy

/-- The bounded-above graded-piece homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) :
    (Minus.GradedPiece.homotopy C p).CommShift ℤ :=
  inferInstanceAs
    ((((FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryMinus ⋙
      DerivedCategory.Minus.Qh C)).CommShift ℤ)

/-- The bounded-above graded-piece homotopy functor is exact. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) :
    (Minus.GradedPiece.homotopy C p).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryMinus ⋙
      DerivedCategory.Minus.Qh C).IsTriangulated)

end Minus.GradedPiece.Homotopy

namespace Minus.GradedPiece.Lift

/-- A bounded-above derived graded-piece lift commutes with integer shifts. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) (h_piece : Minus.GradedPiece.Inverts C p) :
    (Minus.GradedPiece.lift C h_inverts p h_piece).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Minus.QuasiIso C) (Minus.Quotient.functor C h_inverts)
    (Minus.GradedPiece.homotopy C p) h_piece

/-- A bounded-above derived graded-piece lift is exact. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) (h_piece : Minus.GradedPiece.Inverts C p) :
    (Minus.GradedPiece.lift C h_inverts p h_piece).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Minus.QuasiIso C) (Minus.Quotient.functor C h_inverts)
    (Minus.GradedPiece.homotopy C p) h_piece

end Minus.GradedPiece.Lift

namespace Minus.Forget.Homotopy

/-- The bounded-above forgetful homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
noncomputable instance commShift : (Minus.Forget.homotopy C).CommShift ℤ :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryMinus ⋙
      DerivedCategory.Minus.Qh C).CommShift ℤ)

/-- The bounded-above forgetful homotopy functor is exact. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
instance isTriangulated : (Minus.Forget.homotopy C).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryMinus ⋙
      DerivedCategory.Minus.Qh C).IsTriangulated)

end Minus.Forget.Homotopy

namespace Minus.Forget.Lift

/-- A bounded-above derived forgetful lift commutes with integer shifts. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
noncomputable instance commShift (h_forget : Minus.Forget.Inverts C) :
    (Minus.Forget.lift C h_inverts h_forget).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Minus.QuasiIso C) (Minus.Quotient.functor C h_inverts)
    (Minus.Forget.homotopy C) h_forget

/-- A bounded-above derived forgetful lift is exact. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
instance isTriangulated (h_forget : Minus.Forget.Inverts C) :
    (Minus.Forget.lift C h_inverts h_forget).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Minus.QuasiIso C) (Minus.Quotient.functor C h_inverts)
    (Minus.Forget.homotopy C) h_forget

end Minus.Forget.Lift

end CategoryTheory.FilteredObject.FiniteDerived
