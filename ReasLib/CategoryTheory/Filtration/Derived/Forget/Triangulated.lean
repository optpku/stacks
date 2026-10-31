/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Forget
public import ReasLib.CategoryTheory.Filtration.Derived.Triangulated
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated structure on the finite derived forgetful functor

This leaf adds shift and exactness infrastructure to the localization lift from
`Derived.Forget`.  Keeping it separate lets clients use the underlying functor and its
factorization without importing the Verdier enhancement of the finite filtered derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory C]

namespace Forget

/-- Forgetting a finite filtration and passing to the ordinary derived category is exact on the
homotopy category. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance Homotopy.isTriangulated :
    (homotopy C).IsTriangulated :=
  inferInstanceAs
    ((Finite.Forget.homotopy C ⋙ DerivedCategory.Qh).IsTriangulated)

/-- The derived forgetful lift carries the canonical shift comparison induced by localization. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance Lift.commShift
    (h_inverts : Inverts C) :
    (lift C h_inverts).CommShift ℤ :=
  CategoryTheory.Localization.liftCommShift
    (FilteredObject.Finite.Homotopy.quasiIso C) (Quotient.functor C) (homotopy C) h_inverts

/-- The forgetful functor on the finite filtered derived category is exact once the chosen
inversion certificate is supplied. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance Lift.isTriangulated
    (h_inverts : Inverts C) :
    (lift C h_inverts).IsTriangulated :=
  CategoryTheory.Localization.lift_isTriangulated
    (FilteredObject.Finite.Homotopy.quasiIso C) (Quotient.functor C) (homotopy C) h_inverts

namespace FacIso

/-- The forward morphism of the canonical derived-forgetful factorization commutes with
integer shifts. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance homCommShift
    (h_inverts : Inverts C) :
    NatTrans.CommShift (facIso C h_inverts).hom ℤ := sorry

/-- The inverse morphism of the canonical derived-forgetful factorization commutes with
integer shifts. -/
@[stacks 05S3 "finite filtered forgetful derived functor"]
noncomputable instance invCommShift
    (h_inverts : Inverts C) :
    NatTrans.CommShift (facIso C h_inverts).inv ℤ := sorry

end FacIso

end Forget

end CategoryTheory.FilteredObject.FiniteDerived
