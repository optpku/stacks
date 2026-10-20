module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Inferring bounded derived definedness

For a one-sided bounded homotopy object, unbounded source-definedness canonically supplies the
corresponding bounded source-definedness.  Only this downstream direction is registered, so the
equivalence theorems do not create typeclass loops.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- Stacks 05T5: unbounded source-definedness at a bounded-below object supplies bounded-below
source-definedness.  The reverse direction remains available through `DefinedAt.iff_boundedBelow`
but is deliberately not an instance. -/
@[stacks 05T5 "infer bounded-below source-definedness"]
instance (priority := 900) RightDerived.DefinedAt.boundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

/-- Stacks 05T5: unbounded source-definedness at a bounded-above object supplies bounded-above
source-definedness.  The reverse direction remains available through `DefinedAt.iff_boundedAbove`
but is deliberately not an instance. -/
@[stacks 05T5 "infer bounded-above source-definedness"]
instance (priority := 900) LeftDerived.DefinedAt.boundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K := sorry

/-- Stacks 05T5: bounded-below source-definedness can be transported explicitly to the
unbounded homotopy category. This direction is deliberately not an instance. -/
@[stacks 05T5 "unbounded source-definedness from bounded-below source-definedness"]
theorem RightDerived.DefinedAt.ofBoundedBelow
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K] :
    RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj := sorry

/-- Stacks 05T5: bounded-above source-definedness can be transported explicitly to the
unbounded homotopy category. This direction is deliberately not an instance. -/
@[stacks 05T5 "unbounded source-definedness from bounded-above source-definedness"]
theorem LeftDerived.DefinedAt.ofBoundedAbove
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K] :
    LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj := sorry

/-- Stacks 05T5: an everywhere source-defined ambient right-derived functor is source-defined
on every bounded-below object after passage to the bounded model. -/
@[stacks 05T5 "infer everywhere bounded-below source-definedness"]
instance (priority := 900) RightDerived.EverywhereDefined.boundedBelow
    (F : A ⥤ B) [F.Additive]
    [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- Stacks 05T5: an everywhere source-defined ambient left-derived functor is source-defined
on every bounded-above object after passage to the bounded model. -/
@[stacks 05T5 "infer everywhere bounded-above source-definedness"]
instance (priority := 900) LeftDerived.EverywhereDefined.boundedAbove
    (F : A ⥤ B) [F.Additive]
    [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    LeftDerived.EverywhereDefined F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) := sorry

section

variable (F : A ⥤ B) [F.Additive]

variable (K : HomotopyCategory.Plus A)
  [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ)) K.obj]

#synth RightDerived.DefinedAt F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A) K

variable (L : HomotopyCategory.Minus A)
  [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ)) L.obj]

#synth LeftDerived.DefinedAt F.toBoundedAboveDerived
  (HomotopyCategory.Minus.quasiIso A) L

variable [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
  (HomotopyCategory.quasiIso A (up ℤ))]

#synth RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)

end

section

variable (F : A ⥤ B) [F.Additive]
  [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
    (HomotopyCategory.quasiIso A (up ℤ))]

#synth LeftDerived.EverywhereDefined F.toBoundedAboveDerived
  (HomotopyCategory.Minus.quasiIso A)

end


end CategoryTheory.Functor
