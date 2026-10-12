/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Value
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of bounded and unbounded derived-value comparisons

The comparison between bounded and unbounded pointwise derived values is natural on the full
subcategory of objects where both presentations are defined.  These equations require only
essential constancy, not the stronger condition that the identity denominator computes the
derived value.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace RightDerived.Value.boundedBelowIso

/-- Stacks 05T5: the forward bounded-below value comparison is natural at objects where both
the bounded and unbounded right-derived values are defined. -/
@[reassoc, stacks 05T5 "bounded-below defined-value comparison naturality"]
theorem hom_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    DerivedCategory.Plus.ι.map
          (RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) f) ≫
        (RightDerived.Value.boundedBelowIso F L).hom =
      (RightDerived.Value.boundedBelowIso F K).hom ≫
        RightDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) f.hom := sorry

/-- Stacks 05T5: the inverses of the bounded-below value comparisons satisfy the reverse
naturality equation wherever both bounded and unbounded values are defined. -/
@[reassoc, stacks 05T5 "bounded-below defined-value inverse naturality"]
theorem inv_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    RightDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) f.hom ≫
        (RightDerived.Value.boundedBelowIso F L).inv =
      (RightDerived.Value.boundedBelowIso F K).inv ≫
        DerivedCategory.Plus.ι.map
          (RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) f) := sorry

end RightDerived.Value.boundedBelowIso

namespace LeftDerived.Value.boundedAboveIso

/-- Stacks 05T5: the forward bounded-above value comparison is natural at objects where both
the bounded and unbounded left-derived values are defined. -/
@[reassoc, stacks 05T5 "bounded-above defined-value comparison naturality"]
theorem hom_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    DerivedCategory.Minus.ι.map
          (LeftDerived.Value.map F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) f) ≫
        (LeftDerived.Value.boundedAboveIso F L).hom =
      (LeftDerived.Value.boundedAboveIso F K).hom ≫
        LeftDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) f.hom := sorry

/-- Stacks 05T5: the inverses of the bounded-above value comparisons satisfy the reverse
naturality equation wherever both bounded and unbounded values are defined. -/
@[reassoc, stacks 05T5 "bounded-above defined-value inverse naturality"]
theorem inv_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    LeftDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) f.hom ≫
        (LeftDerived.Value.boundedAboveIso F L).inv =
      (LeftDerived.Value.boundedAboveIso F K).inv ≫
        DerivedCategory.Minus.ι.map
          (LeftDerived.Value.map F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) f) := sorry

end LeftDerived.Value.boundedAboveIso


end CategoryTheory.Functor
