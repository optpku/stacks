/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Value

/-!
# Explicit Pointwise Derived-Value Comparisons

The canonical comparison at a computing object is usually exposed through a typeclass
argument.  This leaf provides the same data with an explicit computation witness, allowing
downstream APIs to pass named `ComputesAt` theorems directly without installing local instances.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]

namespace RightDerived.ComputesAt

/-- The canonical right-derived value comparison with its computation witness supplied
explicitly. -/
@[stacks 05SX "explicit right-derived value comparison"]
noncomputable def valueIsoOf (X : D) (hX : RightDerived.ComputesAt F S X) :
    F.obj X ≅ RightDerived.Value.obj F S X :=
  @valueIso D D' _ _ F S _ X hX

/-- The forward explicit right-derived comparison is the identity-denominator leg. -/
@[simp, stacks 05SX "explicit right-derived value comparison, hom"]
theorem valueIsoOf_hom (X : D) (hX : RightDerived.ComputesAt F S X) :
    (valueIsoOf F S X hX).hom = RightDerived.Value.ι F S (𝟙 X) (S.id_mem X) := sorry

/-- The inverse explicit right-derived comparison is the inverse identity-denominator leg. -/
@[simp, stacks 05SX "explicit right-derived value comparison, inv"]
theorem valueIsoOf_inv (X : D) (hX : RightDerived.ComputesAt F S X) :
    (valueIsoOf F S X hX).inv =
      @CategoryTheory.inv _ _ _ _
        (RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) inferInstance := sorry

/-- Explicit right-derived value comparisons are natural between computing objects. -/
@[reassoc, stacks 05SX "naturality of explicit right-derived value comparisons"]
theorem valueIsoOf_hom_naturality {X Y : D} (f : X ⟶ Y)
    (hX : RightDerived.ComputesAt F S X) (hY : RightDerived.ComputesAt F S Y) :
    (valueIsoOf F S X hX).hom ≫ RightDerived.Value.map F S f =
      F.map f ≫ (valueIsoOf F S Y hY).hom := sorry

/-- The inverses of explicit right-derived value comparisons satisfy reverse naturality. -/
@[reassoc, stacks 05SX "inverse naturality of explicit right-derived value comparisons"]
theorem valueIsoOf_inv_naturality {X Y : D} (f : X ⟶ Y)
    (hX : RightDerived.ComputesAt F S X) (hY : RightDerived.ComputesAt F S Y) :
    RightDerived.Value.map F S f ≫ (valueIsoOf F S Y hY).inv =
      (valueIsoOf F S X hX).inv ≫ F.map f := sorry

end RightDerived.ComputesAt

namespace LeftDerived.ComputesAt

/-- The canonical left-derived value comparison with its computation witness supplied
explicitly. -/
@[stacks 05SX "explicit left-derived value comparison"]
noncomputable def valueIsoOf (X : D) (hX : LeftDerived.ComputesAt F S X) :
    LeftDerived.Value.obj F S X ≅ F.obj X :=
  @valueIso D D' _ _ F S _ X hX

/-- The forward explicit left-derived comparison is the identity-denominator projection. -/
@[simp, stacks 05SX "explicit left-derived value comparison, hom"]
theorem valueIsoOf_hom (X : D) (hX : LeftDerived.ComputesAt F S X) :
    (valueIsoOf F S X hX).hom = LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) := sorry

/-- The inverse explicit left-derived comparison is the inverse identity-denominator
projection. -/
@[simp, stacks 05SX "explicit left-derived value comparison, inv"]
theorem valueIsoOf_inv (X : D) (hX : LeftDerived.ComputesAt F S X) :
    (valueIsoOf F S X hX).inv =
      @CategoryTheory.inv _ _ _ _
        (LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) inferInstance := sorry

/-- Explicit left-derived value comparisons are natural between computing objects. -/
@[reassoc, stacks 05SX "naturality of explicit left-derived value comparisons"]
theorem valueIsoOf_hom_naturality {X Y : D} (f : X ⟶ Y)
    (hX : LeftDerived.ComputesAt F S X) (hY : LeftDerived.ComputesAt F S Y) :
    LeftDerived.Value.map F S f ≫ (valueIsoOf F S Y hY).hom =
      (valueIsoOf F S X hX).hom ≫ F.map f := sorry

/-- The inverses of explicit left-derived value comparisons satisfy reverse naturality. -/
@[reassoc, stacks 05SX "inverse naturality of explicit left-derived value comparisons"]
theorem valueIsoOf_inv_naturality {X Y : D} (f : X ⟶ Y)
    (hX : LeftDerived.ComputesAt F S X) (hY : LeftDerived.ComputesAt F S Y) :
    F.map f ≫ (valueIsoOf F S Y hY).inv =
      (valueIsoOf F S X hX).inv ≫ LeftDerived.Value.map F S f := sorry

end LeftDerived.ComputesAt

end CategoryTheory.Functor
