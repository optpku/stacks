/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Acyclic.Retract
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-Isomorphisms in Bounded Homotopy Categories

@stack 05RW

The namespaces `HomotopyCategory.Plus`, `HomotopyCategory.Minus`, and
`HomotopyCategory.Bounded` own the denominator and acyclic object properties for the three
standard bounded homotopy categories. This leaf supplies computation, shift, saturation, and
triangulation API without introducing a derived category.
-/

open CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty
open ComplexShape

universe v u

namespace CategoryTheory

namespace HomotopyCategory.Plus

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Acyclic objects in `K⁺(A)`, obtained by restricting the ambient acyclic property. -/
@[stacks 05RW "bounded-below acyclic homotopy objects"]
abbrev acyclic : ObjectProperty (HomotopyCategory.Plus A) :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage (HomotopyCategory.plus A).ι

/-- Membership in the bounded-below acyclic property is computed by the ambient inclusion. -/
theorem acyclic_iff (X : HomotopyCategory.Plus A) :
    acyclic A X ↔ HomotopyCategory.subcategoryAcyclic A X.obj := sorry

/-- Stacks 05RW: the bounded-below acyclic Verdier system is the canonical bounded-below
quasi-isomorphism property. -/
@[stacks 05RW "bounded-below acyclic Verdier system"]
theorem acyclic_trW_eq_quasiIso :
    (acyclic A).trW = HomotopyCategory.Plus.quasiIso A := sorry

/-- Bounded-below homotopy quasi-isomorphisms form a saturated multiplicative system. -/
instance quasiIso_isSaturatedMultiplicativeSystem :
    (HomotopyCategory.Plus.quasiIso A).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded-below homotopy quasi-isomorphisms are compatible with the triangulation. -/
instance quasiIso_isCompatibleWithTriangulation :
    (HomotopyCategory.Plus.quasiIso A).IsCompatibleWithTriangulation := sorry

end HomotopyCategory.Plus

namespace HomotopyCategory.Minus

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Quasi-isomorphisms in `K⁻(A)`, obtained by restricting ambient homotopy
quasi-isomorphisms. -/
@[stacks 05RW "bounded-above homotopy quasi-isomorphisms"]
abbrev quasiIso : MorphismProperty (HomotopyCategory.Minus A) :=
  (HomotopyCategory.quasiIso A (up ℤ)).inverseImage (HomotopyCategory.minus A).ι

/-- Acyclic objects in `K⁻(A)`, obtained by restricting the ambient acyclic property. -/
@[stacks 05RW "bounded-above acyclic homotopy objects"]
abbrev acyclic : ObjectProperty (HomotopyCategory.Minus A) :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage (HomotopyCategory.minus A).ι

/-- Membership in bounded-above quasi-isomorphisms is computed by the ambient inclusion. -/
theorem quasiIso_iff {X Y : HomotopyCategory.Minus A} (f : X ⟶ Y) :
    quasiIso A f ↔
      HomotopyCategory.quasiIso A (up ℤ) ((HomotopyCategory.minus A).ι.map f) := sorry

/-- Membership in the bounded-above acyclic property is computed by the ambient inclusion. -/
theorem acyclic_iff (X : HomotopyCategory.Minus A) :
    acyclic A X ↔ HomotopyCategory.subcategoryAcyclic A X.obj := sorry

/-- Stacks 05RW: the bounded-above acyclic Verdier system is the canonical bounded-above
quasi-isomorphism property. -/
@[stacks 05RW "bounded-above acyclic Verdier system"]
theorem acyclic_trW_eq_quasiIso :
    (acyclic A).trW = quasiIso A := sorry

/-- Bounded-above homotopy quasi-isomorphisms are compatible with cohomological shifts. -/
noncomputable instance quasiIso_isCompatibleWithShift :
    (quasiIso A).IsCompatibleWithShift ℤ := sorry

/-- Bounded-above homotopy quasi-isomorphisms form a saturated multiplicative system. -/
instance quasiIso_isSaturatedMultiplicativeSystem :
    (quasiIso A).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded-above homotopy quasi-isomorphisms are compatible with the triangulation. -/
instance quasiIso_isCompatibleWithTriangulation :
    (quasiIso A).IsCompatibleWithTriangulation := sorry

end HomotopyCategory.Minus

namespace HomotopyCategory.Bounded

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Quasi-isomorphisms in `Kᵇ(A)`, obtained by restricting ambient homotopy
quasi-isomorphisms. -/
@[stacks 05RW "bounded homotopy quasi-isomorphisms"]
abbrev quasiIso : MorphismProperty (HomotopyCategory.Bounded A) :=
  (HomotopyCategory.quasiIso A (up ℤ)).inverseImage (HomotopyCategory.bounded A).ι

/-- Acyclic objects in `Kᵇ(A)`, obtained by restricting the ambient acyclic property. -/
@[stacks 05RW "bounded acyclic homotopy objects"]
abbrev acyclic : ObjectProperty (HomotopyCategory.Bounded A) :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage (HomotopyCategory.bounded A).ι

/-- Membership in bounded quasi-isomorphisms is computed by the ambient inclusion. -/
theorem quasiIso_iff {X Y : HomotopyCategory.Bounded A} (f : X ⟶ Y) :
    quasiIso A f ↔
      HomotopyCategory.quasiIso A (up ℤ) ((HomotopyCategory.bounded A).ι.map f) := sorry

/-- Membership in the bounded acyclic property is computed by the ambient inclusion. -/
theorem acyclic_iff (X : HomotopyCategory.Bounded A) :
    acyclic A X ↔ HomotopyCategory.subcategoryAcyclic A X.obj := sorry

/-- Stacks 05RW: the bounded acyclic Verdier system is the canonical bounded
quasi-isomorphism property. -/
@[stacks 05RW "bounded acyclic Verdier system"]
theorem acyclic_trW_eq_quasiIso :
    (acyclic A).trW = quasiIso A := sorry

/-- Bounded homotopy quasi-isomorphisms are compatible with cohomological shifts. -/
noncomputable instance quasiIso_isCompatibleWithShift :
    (quasiIso A).IsCompatibleWithShift ℤ := sorry

/-- Bounded homotopy quasi-isomorphisms form a saturated multiplicative system. -/
instance quasiIso_isSaturatedMultiplicativeSystem :
    (quasiIso A).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded homotopy quasi-isomorphisms are compatible with the triangulation. -/
instance quasiIso_isCompatibleWithTriangulation :
    (quasiIso A).IsCompatibleWithTriangulation := sorry

end HomotopyCategory.Bounded

scoped notation "Qis⁺(" A:arg ")" => HomotopyCategory.Plus.quasiIso A
scoped notation "Qis⁻(" A:arg ")" => HomotopyCategory.Minus.quasiIso A
scoped notation "Qisᵇ(" A:arg ")" => HomotopyCategory.Bounded.quasiIso A
scoped notation "Ac⁺(" A:arg ")" => HomotopyCategory.Plus.acyclic A
scoped notation "Ac⁻(" A:arg ")" => HomotopyCategory.Minus.acyclic A
scoped notation "Acᵇ(" A:arg ")" => HomotopyCategory.Bounded.acyclic A


end CategoryTheory
