/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import ReasLib.CategoryTheory.Abelian.Extension.Yoneda.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Yoneda Extensions and Higher Ext

This file compares positive-degree Yoneda extensions with the canonical derived-category groups
`Ext B A n`.  The comparison is recursive: degree one uses fixed-endpoint extension classes, and
each successor step composes with the short exact sequence removed by `Quotient.obj`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian

noncomputable section

universe w v u

namespace CategoryTheory.YonedaExtension

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A B : C}

namespace Degree

/-- Coercion from positive degrees to natural degrees preserves a successor step. -/
theorem succ (n : ℕ+) : (n : ℕ) + 1 = ((n + 1 : ℕ+) : ℕ) := sorry

end Degree

/-- The recursive comparison from degree-`n` Yoneda extensions to canonical `Ext` classes. -/
@[no_expose]
noncomputable def toExtAux (n : ℕ+) :
    ∀ {X Y : C}, YonedaExtension X Y n → Ext Y X n :=
  @PNat.recOn n
    (fun m ↦ ∀ {X Y : C}, YonedaExtension X Y m → Ext Y X m)
    (fun {X Y} E ↦
      ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass X Y))
    (fun m ih {_ _} E ↦
      (ih (Quotient.obj E)).comp (Quotient.head E).extClass (Degree.succ m))

/-- The canonical comparison from degree-`n` Yoneda extensions of `B` by `A` to
`Ext B A n`. -/
@[stacks 06XU]
noncomputable def toExt {n : ℕ+} (E : YonedaExtension A B n) : Ext B A n :=
  toExtAux n E

/-- In degree one, `toExt` is the canonical class of the underlying short exact extension. -/
@[simp, stacks 06XU]
theorem toExt_one (E : YonedaExtension A B 1) :
    toExt E = ExtensionClass.toExt (⟦E.toExtension⟧ : ExtensionClass A B) := sorry

/-- At a successor degree, `toExt` is obtained by composing the quotient extension class with
the short exact sequence removed from its head. -/
@[stacks 06XU]
theorem toExt_succ {n : ℕ+} (E : YonedaExtension A B (n + 1)) :
    toExt E =
      (toExt (Quotient.obj E)).comp (Quotient.head E).extClass (Degree.succ n) := sorry

/-- Every positive-degree `Ext` class is represented by a Yoneda extension. -/
@[stacks 06XU]
theorem toExt_surjective (n : ℕ+) :
    Function.Surjective (toExt : YonedaExtension A B n → Ext B A n) := sorry

/-- Equivalent Yoneda extensions determine the same canonical `Ext` class. -/
theorem toExt_eq_of_equivalent {n : ℕ+} {E E' : YonedaExtension A B n}
    (h : Equivalent E E') :
    toExt E = toExt E' := sorry

/-- Equality of canonical `Ext` classes is detected by Yoneda equivalence. -/
theorem equivalent_of_toExt_eq {n : ℕ+} {E E' : YonedaExtension A B n}
    (h : toExt E = toExt E') :
    Equivalent E E' := sorry

/-- Two positive-degree Yoneda extensions are equivalent exactly when they represent the same
canonical `Ext` class. -/
@[stacks 06XU]
theorem equivalent_iff_toExt_eq {n : ℕ+} (E E' : YonedaExtension A B n) :
    Equivalent E E' ↔ toExt E = toExt E' := sorry

end CategoryTheory.YonedaExtension
