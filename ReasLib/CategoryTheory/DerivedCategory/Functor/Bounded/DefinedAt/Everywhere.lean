/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Globally natural bounded value comparisons

When the ambient derived functor is source-defined everywhere, its bounded and unbounded
pointwise-value functors are canonically naturally isomorphic after applying the bounded derived
inclusion.  The required bounded source-definedness is inferred automatically.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace RightDerived.Value

namespace boundedBelowNatIso

/-- Naturality of the bounded-below comparison between the globally defined pointwise-value
functors. -/
@[stacks 05T5 "bounded-below value-functor comparison naturality"]
theorem naturality (F : A ⥤ B) [F.Additive]
    [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L) :
    (RightDerived.Value.functor F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A) ⋙ DerivedCategory.Plus.ι).map f ≫
        (boundedBelowIso F L).hom =
      (boundedBelowIso F K).hom ≫
        (HomotopyCategory.Plus.ι A ⋙
          RightDerived.Value.functor (Functor.Homotopy.toDerived F)
            (HomotopyCategory.quasiIso A (up ℤ))).map f := sorry

end boundedBelowNatIso

/-- Stacks 05T5: the bounded-below pointwise right-derived value functor agrees naturally with
the restriction of the ambient pointwise right-derived value functor. -/
@[stacks 05T5 "bounded-below pointwise right-derived value natural isomorphism"]
noncomputable def boundedBelowNatIso (F : A ⥤ B) [F.Additive]
    [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    RightDerived.Value.functor F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι A ⋙
        RightDerived.Value.functor (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) :=
  NatIso.ofComponents (fun K => boundedBelowIso F K)
    (fun f => boundedBelowNatIso.naturality F f)

namespace boundedBelowNatIso

/-- The forward component of the global bounded-below comparison is the objectwise canonical
bounded/unbounded value comparison. -/
@[simp, stacks 05T5 "bounded-below value natural isomorphism component"]
theorem hom_app (F : A ⥤ B) [F.Additive]
    [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory.Plus A) :
    (boundedBelowNatIso F).hom.app K = (boundedBelowIso F K).hom := sorry

/-- The inverse component of the global bounded-below comparison is the inverse objectwise
canonical comparison. -/
@[simp, stacks 05T5 "inverse bounded-below value natural isomorphism component"]
theorem inv_app (F : A ⥤ B) [F.Additive]
    [RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory.Plus A) :
    (boundedBelowNatIso F).inv.app K = (boundedBelowIso F K).inv := sorry

end boundedBelowNatIso

end RightDerived.Value

namespace LeftDerived.Value

namespace boundedAboveNatIso

/-- Naturality of the bounded-above comparison between the globally defined pointwise-value
functors. -/
@[stacks 05T5 "bounded-above value-functor comparison naturality"]
theorem naturality (F : A ⥤ B) [F.Additive]
    [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L) :
    (LeftDerived.Value.functor F.toBoundedAboveDerived
          (HomotopyCategory.Minus.quasiIso A) ⋙ DerivedCategory.Minus.ι).map f ≫
        (boundedAboveIso F L).hom =
      (boundedAboveIso F K).hom ≫
        (HomotopyCategory.Minus.ι A ⋙
          LeftDerived.Value.functor (Functor.Homotopy.toDerived F)
            (HomotopyCategory.quasiIso A (up ℤ))).map f := sorry

end boundedAboveNatIso

/-- Stacks 05T5: the bounded-above pointwise left-derived value functor agrees naturally with
the restriction of the ambient pointwise left-derived value functor. -/
@[stacks 05T5 "bounded-above pointwise left-derived value natural isomorphism"]
noncomputable def boundedAboveNatIso (F : A ⥤ B) [F.Additive]
    [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    LeftDerived.Value.functor F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) ⋙ DerivedCategory.Minus.ι ≅
      HomotopyCategory.Minus.ι A ⋙
        LeftDerived.Value.functor (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) :=
  NatIso.ofComponents (fun K => boundedAboveIso F K)
    (fun f => boundedAboveNatIso.naturality F f)

namespace boundedAboveNatIso

/-- The forward component of the global bounded-above comparison is the objectwise canonical
bounded/unbounded value comparison. -/
@[simp, stacks 05T5 "bounded-above value natural isomorphism component"]
theorem hom_app (F : A ⥤ B) [F.Additive]
    [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory.Minus A) :
    (boundedAboveNatIso F).hom.app K = (boundedAboveIso F K).hom := sorry

/-- The inverse component of the global bounded-above comparison is the inverse objectwise
canonical comparison. -/
@[simp, stacks 05T5 "inverse bounded-above value natural isomorphism component"]
theorem inv_app (F : A ⥤ B) [F.Additive]
    [LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory.Minus A) :
    (boundedAboveNatIso F).inv.app K = (boundedAboveIso F K).inv := sorry

end boundedAboveNatIso

end LeftDerived.Value

end CategoryTheory.Functor
