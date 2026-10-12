/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting bounded and unbounded computing objects

Unbounded computation canonically supplies bounded computation and is therefore registered as a
one-way instance.  The converse is exposed as an ordinary theorem, so applications can transport
a known bounded computing object without creating a typeclass loop.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- A bounded-below object which computes the unbounded right-derived value also computes the
bounded-below right-derived value. -/
@[stacks 05T5]
instance (priority := 900) RightDerived.ComputesAt.boundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

/-- A bounded-above object which computes the unbounded left-derived value also computes the
bounded-above left-derived value. -/
@[stacks 05T5]
instance (priority := 900) LeftDerived.ComputesAt.boundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K := sorry

/-- Stacks 05T5: bounded-below computation can be transported explicitly to unbounded
computation.  This direction is deliberately not an instance. -/
@[stacks 05T5 "unbounded computation from bounded-below computation"]
theorem RightDerived.ComputesAt.ofBoundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K] :
    RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj := sorry

/-- Stacks 05T5: bounded-above computation can be transported explicitly to unbounded
computation.  This direction is deliberately not an instance. -/
@[stacks 05T5 "unbounded computation from bounded-above computation"]
theorem LeftDerived.ComputesAt.ofBoundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K] :
    LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj := sorry

section

variable (F : A ⥤ B) [F.Additive]

variable (K : HomotopyCategory.Plus A)
  [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ)) K.obj]

#synth RightDerived.ComputesAt F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A) K

variable (L : HomotopyCategory.Minus A)
  [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ)) L.obj]

#synth LeftDerived.ComputesAt F.toBoundedAboveDerived
  (HomotopyCategory.Minus.quasiIso A) L

end


end CategoryTheory.Functor
