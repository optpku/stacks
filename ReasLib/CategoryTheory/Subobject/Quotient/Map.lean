/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Subobject Quotients

This leaf provides the common construction of a morphism `Y / X ⟶ Y' / X'` from an ambient
morphism which preserves both the numerator and denominator subobjects.  The underlying quotient
objects remain the canonical cokernels of the corresponding inclusions; this module adds only
the high-level constructor and its projection-level specification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Subobject.Quotient

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The restrictions of an ambient morphism to the numerator and denominator subobjects form
the defining commutative square of their quotient cokernels. -/
@[stacks 012M "naturality square for an ambient subobject quotient map"]
theorem factorThru_square {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} (f : A ⟶ B)
    (h_numerator : Y'.Factors (Y.arrow ≫ f))
    (h_denominator : X'.Factors (X.arrow ≫ f)) :
    Subobject.ofLE X Y hXY ≫ Y'.factorThru (Y.arrow ≫ f) h_numerator =
      X'.factorThru (X.arrow ≫ f) h_denominator ≫ Subobject.ofLE X' Y' hX'Y' := sorry

/-- Construct a map of subobject quotients from an explicit commutative square between their
denominator and numerator representatives.  Keeping both restricted maps as data prevents the
quotient morphism from choosing them through an existential factorization proof. -/
@[stacks 012M "subobject quotient map from an explicit square"]
noncomputable def map {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'}
    (denominator : (X : C) ⟶ (X' : C)) (numerator : (Y : C) ⟶ (Y' : C))
    (h_comm : Subobject.ofLE X Y hXY ≫ numerator =
      denominator ≫ Subobject.ofLE X' Y' hX'Y') :
    cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y') :=
  cokernel.map
    (Subobject.ofLE X Y hXY) (Subobject.ofLE X' Y' hX'Y')
    denominator numerator h_comm

/-- The explicit-square quotient map is characterized by naturality of quotient projections. -/
@[reassoc (attr := simp), stacks 012M "subobject quotient projection map"]
theorem π_map {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'}
    (denominator : (X : C) ⟶ (X' : C)) (numerator : (Y : C) ⟶ (Y' : C))
    (h_comm : Subobject.ofLE X Y hXY ≫ numerator =
      denominator ≫ Subobject.ofLE X' Y' hX'Y') :
    cokernel.π (Subobject.ofLE X Y hXY) ≫ map denominator numerator h_comm =
      numerator ≫ cokernel.π (Subobject.ofLE X' Y' hX'Y') := sorry

/-- A morphism between quotient cokernels is induced by a map between their numerator
subobjects when it commutes with the canonical quotient projections. -/
@[stacks 012M "induced subobject quotient map"]
def IsInduced {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} (q : (Y : C) ⟶ (Y' : C))
    (g : cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y')) : Prop :=
  cokernel.π (Subobject.ofLE X Y hXY) ≫ g = q ≫ cokernel.π (Subobject.ofLE X' Y' hX'Y')

/-- The quotient map built from an explicit square is induced by its numerator map. -/
@[stacks 012M "explicit-square subobject quotient map is induced"]
theorem map_isInduced {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'}
    (denominator : (X : C) ⟶ (X' : C)) (numerator : (Y : C) ⟶ (Y' : C))
    (h_comm : Subobject.ofLE X Y hXY ≫ numerator =
      denominator ≫ Subobject.ofLE X' Y' hX'Y') :
    IsInduced (hXY := hXY) (hX'Y' := hX'Y') numerator
      (map denominator numerator h_comm) := sorry

/-- An ambient morphism preserving numerator and denominator subobjects admits an induced map
between the corresponding quotient objects. This is proposition-valued, so it does not select
restricted morphism data from the factorization witnesses. -/
@[stacks 012M "existence of an ambient subobject quotient map"]
theorem existsMap {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} (f : A ⟶ B)
    (h_numerator : Y'.Factors (Y.arrow ≫ f))
    (h_denominator : X'.Factors (X.arrow ≫ f)) :
    ∃ g : cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y'),
      IsInduced (hXY := hXY) (hX'Y' := hX'Y')
        (Y'.factorThru (Y.arrow ≫ f) h_numerator) g := sorry

/-- An ambient morphism preserving numerator and denominator subobjects induces a unique
quotient map once its numerator restriction is fixed. -/
@[stacks 012M "unique ambient subobject quotient map"]
theorem existsUniqueMap {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} (f : A ⟶ B)
    (h_numerator : Y'.Factors (Y.arrow ≫ f))
    (h_denominator : X'.Factors (X.arrow ≫ f)) :
    ∃! g : cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y'),
      IsInduced (hXY := hXY) (hX'Y' := hX'Y')
        (Y'.factorThru (Y.arrow ≫ f) h_numerator) g := sorry

namespace IsInduced

/-- The identity of a subobject quotient is induced by the identity of its numerator. -/
@[simp, stacks 012M "identity induced subobject quotient map"]
theorem id {A : C} {X Y : Subobject A} {hXY : X ≤ Y} :
    IsInduced (hXY := hXY) (𝟙 (Y : C)) (𝟙 (cokernel (Subobject.ofLE X Y hXY))) := sorry

/-- The composite of induced subobject quotient maps is induced by the composite numerator map. -/
@[stacks 012M "composition of induced subobject quotient maps"]
theorem comp {A B D : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {X'' Y'' : Subobject D} {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} {hX''Y'' : X'' ≤ Y''}
    {q : (Y : C) ⟶ (Y' : C)} {q' : (Y' : C) ⟶ (Y'' : C)}
    {f : cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y')}
    {g : cokernel (Subobject.ofLE X' Y' hX'Y') ⟶ cokernel (Subobject.ofLE X'' Y'' hX''Y'')}
    (hf : IsInduced (hXY := hXY) (hX'Y' := hX'Y') q f)
    (hg : IsInduced (hXY := hX'Y') (hX'Y' := hX''Y'') q' g) :
    IsInduced (hXY := hXY) (hX'Y' := hX''Y'') (q ≫ q') (f ≫ g) := sorry

/-- Two maps between fixed subobject quotients induced by the same numerator map are equal. -/
@[stacks 012M "uniqueness of induced subobject quotient maps"]
theorem ext {A B : C} {X Y : Subobject A} {X' Y' : Subobject B}
    {hXY : X ≤ Y} {hX'Y' : X' ≤ Y'} {q : (Y : C) ⟶ (Y' : C)}
    {f g : cokernel (Subobject.ofLE X Y hXY) ⟶ cokernel (Subobject.ofLE X' Y' hX'Y')}
    (hf : IsInduced q f) (hg : IsInduced q g) : f = g := sorry

end IsInduced

/-! ## Reusable API checks -/

end Subobject.Quotient

end CategoryTheory
