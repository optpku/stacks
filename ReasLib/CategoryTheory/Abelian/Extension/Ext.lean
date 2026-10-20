module

public import ReasLib.CategoryTheory.Abelian.Extension.BaerSum
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

@[expose] public section

/-!
# The Ext-One Class of a Fixed-Endpoint Extension

This module connects the endpoint-fixed quotient `ExtensionClass A B` with the canonical
degree-one derived-category object `Ext B A 1`.  Pullback and pushout are expressed as the
standard contravariant and covariant endpoint actions on `Ext`.
-/

namespace CategoryTheory

universe w v u

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A B : C}

namespace Extension

variable {S T : Extension A B}
variable {A' B' : C}

/-- The canonical degree-one `Ext` class of a fixed-endpoint short exact extension. -/
@[stacks 010L "Ext-one class of a fixed-endpoint extension"]
noncomputable abbrev extClass (S : Extension A B) : Ext B A 1 :=
  S.shortExact.extClass

/-- Isomorphic fixed-endpoint extensions determine equal canonical `Ext¹` classes. -/
theorem extClass_eq_of_isIsomorphic (h : IsIsomorphic S T) :
    S.extClass = T.extClass := sorry

/-- An extension whose quotient morphism has a section represents zero in `Ext¹`. -/
theorem extClass_eq_zero_of_section (S : Extension A B) (s : B ⟶ S.E)
    (hs : s ≫ S.g = 𝟙 B) : S.extClass = 0 := sorry

/-- The `Ext¹` class of a pullback extension is precomposition in the first variable. -/
@[simp]
theorem pullback_extClass (u : B' ⟶ B) (S : Extension A B) :
    (pullback u S).shortExact.extClass =
      (Ext.mk₀ u).precomp A (zero_add 1) S.shortExact.extClass := sorry

/-- The `Ext¹` class of a pushout extension is postcomposition in the second variable. -/
@[simp]
theorem pushout_extClass (a : A ⟶ A') (S : Extension A B) :
    (pushout a S).shortExact.extClass =
      (Ext.mk₀ a).postcomp B (add_zero 1) S.shortExact.extClass := sorry

/-- The `Ext¹` class of a Baer sum is the sum of the two extension classes. -/
@[simp]
theorem baerSum_extClass (S T : Extension A B) :
    (baerSum S T).shortExact.extClass = S.shortExact.extClass + T.shortExact.extClass := sorry

end Extension

namespace ExtensionClass

variable {A' B' : C}

/-- The canonical bridge from endpoint-fixed extension classes to `Ext¹(B, A)`. -/
@[stacks 010L "extension-class to Ext-one bridge"]
noncomputable def toExt : ExtensionClass A B → Ext B A 1 :=
  _root_.Quotient.lift (fun S ↦ S.extClass) fun _ _ h ↦
    Extension.extClass_eq_of_isIsomorphic h

/-- The canonical `Ext¹` bridge computes on an extension representative. -/
@[simp]
theorem toExt_mk (S : Extension A B) :
    toExt (⟦S⟧ : ExtensionClass A B) = S.extClass := sorry

/-- Pullback of extension classes is precomposition in the first variable of `Ext¹`. -/
@[simp]
theorem toExt_pullback (u : B' ⟶ B) (xi : ExtensionClass A B) :
    toExt (pullback u xi) = (Ext.mk₀ u).precomp A (zero_add 1) (toExt xi) := sorry

/-- Pushout of extension classes is postcomposition in the second variable of `Ext¹`. -/
@[simp]
theorem toExt_pushout (a : A ⟶ A') (xi : ExtensionClass A B) :
    toExt (pushout a xi) = (Ext.mk₀ a).postcomp B (add_zero 1) (toExt xi) := sorry

/-- The split extension class maps to zero in `Ext¹`. -/
@[simp]
theorem toExt_zero : toExt (0 : ExtensionClass A B) = 0 := sorry

/-- The canonical `Ext¹` bridge preserves negation. -/
@[simp]
theorem toExt_neg (xi : ExtensionClass A B) : toExt (-xi) = -toExt xi := sorry

/-- The canonical `Ext¹` bridge takes Baer sums to addition. -/
@[simp]
theorem toExt_baerSum (xi eta : ExtensionClass A B) :
    toExt (baerSum xi eta) = toExt xi + toExt eta := sorry

/-- The canonical `Ext¹` bridge preserves the chosen addition on extension classes. -/
@[simp]
theorem toExt_add (xi eta : ExtensionClass A B) :
    toExt (xi + eta) = toExt xi + toExt eta := sorry

end ExtensionClass

end

end CategoryTheory
