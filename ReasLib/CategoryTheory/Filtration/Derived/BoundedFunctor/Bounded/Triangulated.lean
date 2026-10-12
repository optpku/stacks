/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Bounded
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact bounded finite filtered derived functors

This leaf registers the shift and exactness structures of the bounded graded-piece and forgetful
homotopy functors and transports them through their explicit localization lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Bounded.GradedPiece.Homotopy

/-- The bounded graded-piece homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) :
    (Bounded.GradedPiece.homotopy C p).CommShift ℤ :=
  inferInstanceAs
    ((((FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryBounded ⋙
      DerivedCategory.Bounded.Qh C)).CommShift ℤ)

/-- The bounded graded-piece homotopy functor is exact. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) :
    (Bounded.GradedPiece.homotopy C p).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryBounded ⋙
      DerivedCategory.Bounded.Qh C).IsTriangulated)

end Bounded.GradedPiece.Homotopy

namespace Bounded.GradedPiece.Lift

/-- A bounded derived graded-piece lift commutes with integer shifts. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
noncomputable instance commShift (p : ℤ) (h_piece : Bounded.GradedPiece.Inverts C p) :
    (Bounded.GradedPiece.lift C h_inverts p h_piece).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Bounded.QuasiIso C) (Bounded.Quotient.functor C h_inverts)
    (Bounded.GradedPiece.homotopy C p) h_piece

/-- A bounded derived graded-piece lift is exact. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
instance isTriangulated (p : ℤ) (h_piece : Bounded.GradedPiece.Inverts C p) :
    (Bounded.GradedPiece.lift C h_inverts p h_piece).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Bounded.QuasiIso C) (Bounded.Quotient.functor C h_inverts)
    (Bounded.GradedPiece.homotopy C p) h_piece

end Bounded.GradedPiece.Lift

namespace Bounded.Forget.Homotopy

/-- The bounded forgetful homotopy functor commutes with integer shifts. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
noncomputable instance commShift : (Bounded.Forget.homotopy C).CommShift ℤ :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryBounded ⋙
      DerivedCategory.Bounded.Qh C).CommShift ℤ)

/-- The bounded forgetful homotopy functor is exact. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
instance isTriangulated : (Bounded.Forget.homotopy C).IsTriangulated :=
  inferInstanceAs
    (((FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryBounded ⋙
      DerivedCategory.Bounded.Qh C).IsTriangulated)

end Bounded.Forget.Homotopy

namespace Bounded.Forget.Lift

/-- A bounded derived forgetful lift commutes with integer shifts. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
noncomputable instance commShift (h_forget : Bounded.Forget.Inverts C) :
    (Bounded.Forget.lift C h_inverts h_forget).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (Bounded.QuasiIso C) (Bounded.Quotient.functor C h_inverts)
    (Bounded.Forget.homotopy C) h_forget

/-- A bounded derived forgetful lift is exact. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
instance isTriangulated (h_forget : Bounded.Forget.Inverts C) :
    (Bounded.Forget.lift C h_inverts h_forget).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (Bounded.QuasiIso C) (Bounded.Quotient.functor C h_inverts)
    (Bounded.Forget.homotopy C) h_forget

end Bounded.Forget.Lift

end CategoryTheory.FilteredObject.FiniteDerived
