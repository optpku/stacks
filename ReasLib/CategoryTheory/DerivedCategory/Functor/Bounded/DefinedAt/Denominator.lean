/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Value
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded value comparisons on denominators

The bounded/unbounded comparison of pointwise derived values is computed directly on the
canonical morphism attached to a quasi-isomorphism.  These formulas hide the corresponding
localization comma object and the ambient image of its denominator.
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

/-- Stacks 05T5: the bounded-below comparison carries the canonical morphism attached to a
bounded-below denominator to the canonical morphism attached to its ambient image. -/
@[reassoc, stacks 05T5 "bounded-below value comparison on a denominator"]
theorem hom_ι (F : A ⥤ B) [F.Additive]
    {K K' : HomotopyCategory.Plus A} (s : K ⟶ K')
    (hs : HomotopyCategory.Plus.quasiIso A s)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Plus.ι.map
          (RightDerived.Value.ι F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) s hs) ≫
        (RightDerived.Value.boundedBelowIso F K).hom =
      RightDerived.Value.ι (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) s.hom
        ((HomotopyCategory.Plus.Ambient.localizerMorphism A).map s hs) := sorry

/-- Stacks 05T5: the inverse bounded-below comparison carries the ambient canonical morphism
attached to a bounded-below denominator back to the bounded canonical morphism. -/
@[reassoc, stacks 05T5 "inverse bounded-below value comparison on a denominator"]
theorem ι_inv (F : A ⥤ B) [F.Additive]
    {K K' : HomotopyCategory.Plus A} (s : K ⟶ K')
    (hs : HomotopyCategory.Plus.quasiIso A s)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    RightDerived.Value.ι (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) s.hom
          ((HomotopyCategory.Plus.Ambient.localizerMorphism A).map s hs) ≫
        (RightDerived.Value.boundedBelowIso F K).inv =
      DerivedCategory.Plus.ι.map
        (RightDerived.Value.ι F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A) s hs) := sorry

/-- The bounded-below value comparison identifies the two identity-denominator morphisms. -/
@[reassoc, stacks 05T5 "bounded-below value comparison on the identity denominator"]
theorem hom_ι_id (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Plus.ι.map
          (RightDerived.Value.ι F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) (𝟙 K)
            ((HomotopyCategory.Plus.quasiIso A).id_mem K)) ≫
        (RightDerived.Value.boundedBelowIso F K).hom =
      RightDerived.Value.ι (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) (𝟙 K.obj)
        ((HomotopyCategory.quasiIso A (up ℤ)).id_mem K.obj) := sorry

/-- The inverse bounded-below value comparison identifies the two identity-denominator
morphisms. -/
@[reassoc, stacks 05T5 "inverse bounded-below value comparison on the identity denominator"]
theorem ι_id_inv (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    RightDerived.Value.ι (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) (𝟙 K.obj)
          ((HomotopyCategory.quasiIso A (up ℤ)).id_mem K.obj) ≫
        (RightDerived.Value.boundedBelowIso F K).inv =
      DerivedCategory.Plus.ι.map
        (RightDerived.Value.ι F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A) (𝟙 K)
          ((HomotopyCategory.Plus.quasiIso A).id_mem K)) := sorry

end RightDerived.Value.boundedBelowIso

namespace LeftDerived.Value.boundedAboveIso

/-- Stacks 05T5: the bounded-above comparison carries its ambient canonical projection to the
canonical projection attached to the bounded-above denominator. -/
@[reassoc, stacks 05T5 "bounded-above value comparison on a denominator"]
theorem hom_π (F : A ⥤ B) [F.Additive]
    {K' K : HomotopyCategory.Minus A} (s : K' ⟶ K)
    (hs : HomotopyCategory.Minus.quasiIso A s)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    (LeftDerived.Value.boundedAboveIso F K).hom ≫
        LeftDerived.Value.π (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) s.hom
          ((HomotopyCategory.Minus.Ambient.localizerMorphism A).map s hs) =
      DerivedCategory.Minus.ι.map
        (LeftDerived.Value.π F.toBoundedAboveDerived
          (HomotopyCategory.Minus.quasiIso A) s hs) := sorry

/-- Stacks 05T5: the inverse bounded-above comparison carries the bounded canonical projection
back to the ambient canonical projection. -/
@[reassoc, stacks 05T5 "inverse bounded-above value comparison on a denominator"]
theorem inv_π (F : A ⥤ B) [F.Additive]
    {K' K : HomotopyCategory.Minus A} (s : K' ⟶ K)
    (hs : HomotopyCategory.Minus.quasiIso A s)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    (LeftDerived.Value.boundedAboveIso F K).inv ≫
        DerivedCategory.Minus.ι.map
          (LeftDerived.Value.π F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) s hs) =
      LeftDerived.Value.π (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) s.hom
        ((HomotopyCategory.Minus.Ambient.localizerMorphism A).map s hs) := sorry

/-- The bounded-above value comparison identifies the two identity-denominator projections. -/
@[reassoc, stacks 05T5 "bounded-above value comparison on the identity denominator"]
theorem hom_π_id (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    (LeftDerived.Value.boundedAboveIso F K).hom ≫
        LeftDerived.Value.π (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ)) (𝟙 K.obj)
          ((HomotopyCategory.quasiIso A (up ℤ)).id_mem K.obj) =
      DerivedCategory.Minus.ι.map
        (LeftDerived.Value.π F.toBoundedAboveDerived
          (HomotopyCategory.Minus.quasiIso A) (𝟙 K)
          ((HomotopyCategory.Minus.quasiIso A).id_mem K)) := sorry

/-- The inverse bounded-above value comparison identifies the two identity-denominator
projections. -/
@[reassoc, stacks 05T5 "inverse bounded-above value comparison on the identity denominator"]
theorem inv_π_id (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    (LeftDerived.Value.boundedAboveIso F K).inv ≫
        DerivedCategory.Minus.ι.map
          (LeftDerived.Value.π F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) (𝟙 K)
            ((HomotopyCategory.Minus.quasiIso A).id_mem K)) =
      LeftDerived.Value.π (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) (𝟙 K.obj)
        ((HomotopyCategory.quasiIso A (up ℤ)).id_mem K.obj) := sorry

end LeftDerived.Value.boundedAboveIso

end CategoryTheory.Functor
