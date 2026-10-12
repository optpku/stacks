/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.ComputesAt.Instances
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded and Unbounded Values at Computing Objects

For a bounded homotopy object which computes an unbounded pointwise derived value, the bounded
computation is inferred automatically.  The two concrete pointwise values are then compared by
the computation isomorphisms and the canonical inclusion comparison.
-/

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} B]

/-- The canonical comparison from the bounded-below pointwise right-derived value at a
computing object to its unbounded pointwise right-derived value. -/
@[stacks 05T5]
noncomputable def RightDerived.ComputesAt.boundedBelowValueIso
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Plus.ι.obj
        (RightDerived.Value.obj F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A) K) ≅
      RightDerived.Value.obj (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) K.obj :=
  DerivedCategory.Plus.ι.mapIso
      (RightDerived.ComputesAt.valueIso F.toBoundedBelowDerived
        (HomotopyCategory.Plus.quasiIso A) K).symm ≪≫
    (Functor.toBoundedBelowDerived.compInclusionIso F).app K ≪≫
    RightDerived.ComputesAt.valueIso (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj

/-- The computing-object comparison agrees with the canonical comparison requiring only
definedness of the bounded and unbounded localization-indexed diagrams. -/
@[simp, stacks 05T5 "computing bounded-below value comparison agrees with defined-value comparison"]
theorem RightDerived.ComputesAt.boundedBelowValueIso_eq
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Plus A)
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    RightDerived.ComputesAt.boundedBelowValueIso F K =
      RightDerived.Value.boundedBelowIso F K := sorry

namespace RightDerived.ComputesAt.boundedBelowValueIso

/-- The forward bounded-below value comparisons are natural in morphisms between computing
objects. -/
@[reassoc, stacks 05T5 "bounded-below pointwise value comparison naturality"]
theorem hom_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    DerivedCategory.Plus.ι.map
          (RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) f) ≫
        (RightDerived.ComputesAt.boundedBelowValueIso F L).hom =
      (RightDerived.ComputesAt.boundedBelowValueIso F K).hom ≫
        RightDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ))
          f.hom := sorry

/-- The inverse bounded-below value comparisons satisfy the reverse naturality equation. -/
@[reassoc, stacks 05T5 "bounded-below pointwise value comparison inverse naturality"]
theorem inv_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Plus A} (f : K ⟶ L)
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    RightDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ))
          f.hom ≫
        (RightDerived.ComputesAt.boundedBelowValueIso F L).inv =
      (RightDerived.ComputesAt.boundedBelowValueIso F K).inv ≫
        DerivedCategory.Plus.ι.map
          (RightDerived.Value.map F.toBoundedBelowDerived
            (HomotopyCategory.Plus.quasiIso A) f) := sorry

end RightDerived.ComputesAt.boundedBelowValueIso

/-- The canonical comparison from the bounded-above pointwise left-derived value at a computing
object to its unbounded pointwise left-derived value. -/
@[stacks 05T5]
noncomputable def LeftDerived.ComputesAt.boundedAboveValueIso
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Minus.ι.obj
        (LeftDerived.Value.obj F.toBoundedAboveDerived
          (HomotopyCategory.Minus.quasiIso A) K) ≅
      LeftDerived.Value.obj (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) K.obj :=
  DerivedCategory.Minus.ι.mapIso
      (LeftDerived.ComputesAt.valueIso F.toBoundedAboveDerived
        (HomotopyCategory.Minus.quasiIso A) K) ≪≫
    (Functor.toBoundedAboveDerived.compInclusionIso F).app K ≪≫
    (LeftDerived.ComputesAt.valueIso (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj).symm

/-- The computing-object comparison agrees with the canonical comparison requiring only
definedness of the bounded and unbounded localization-indexed diagrams. -/
@[simp, stacks 05T5 "computing bounded-above value comparison agrees with defined-value comparison"]
theorem LeftDerived.ComputesAt.boundedAboveValueIso_eq
    (F : A ⥤ B) [F.Additive] (K : HomotopyCategory.Minus A)
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    LeftDerived.ComputesAt.boundedAboveValueIso F K =
      LeftDerived.Value.boundedAboveIso F K := sorry

namespace LeftDerived.ComputesAt.boundedAboveValueIso

/-- The forward bounded-above value comparisons are natural in morphisms between computing
objects. -/
@[reassoc, stacks 05T5 "bounded-above pointwise value comparison naturality"]
theorem hom_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L)
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    DerivedCategory.Minus.ι.map
          (LeftDerived.Value.map F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) f) ≫
        (LeftDerived.ComputesAt.boundedAboveValueIso F L).hom =
      (LeftDerived.ComputesAt.boundedAboveValueIso F K).hom ≫
        LeftDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ))
          f.hom := sorry

/-- The inverse bounded-above value comparisons satisfy the reverse naturality equation. -/
@[reassoc, stacks 05T5 "bounded-above pointwise value comparison inverse naturality"]
theorem inv_naturality (F : A ⥤ B) [F.Additive]
    {K L : HomotopyCategory.Minus A} (f : K ⟶ L)
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    [LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) L.obj] :
    LeftDerived.Value.map (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ))
          f.hom ≫
        (LeftDerived.ComputesAt.boundedAboveValueIso F L).inv =
      (LeftDerived.ComputesAt.boundedAboveValueIso F K).inv ≫
        DerivedCategory.Minus.ι.map
          (LeftDerived.Value.map F.toBoundedAboveDerived
            (HomotopyCategory.Minus.quasiIso A) f) := sorry

end LeftDerived.ComputesAt.boundedAboveValueIso



end CategoryTheory.Functor
