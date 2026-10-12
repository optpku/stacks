/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.PullPush

@[expose] public section

/-!
# Baer Sums of Fixed-Endpoint Extensions

This module constructs the split extension, negation, biproduct extension, and Baer sum before
passing to endpoint-preserving isomorphism classes.  It deliberately keeps the source-facing
quotient operations separate from the canonical additive structure on `Ext B A 1`.
-/

namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace Extension

variable {S T : Extension A B}

/-- The inclusion and projection of the standard split extension compose to zero. -/
theorem split_zero (A B : C) :
    (biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B) = 0 := sorry

/-- The standard biproduct short complex is short exact. -/
theorem splitShortExact (A B : C) :
    (ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B)
      (split_zero A B)).ShortExact := sorry

/-- The standard split extension of `B` by `A`. -/
@[stacks 010L "split fixed-endpoint extension"]
noncomputable def split (A B : C) : Extension A B :=
  Extension.mk
    (A ⊞ B)
    (biprod.inl : A ⟶ A ⊞ B)
    (biprod.snd : A ⊞ B ⟶ B)
    (split_zero A B)
    (splitShortExact A B)

/-- Negating an extension by pushing it out along `-𝟙 A`. -/
@[stacks 010L "negation of a fixed-endpoint extension"]
noncomputable def neg (S : Extension A B) : Extension A B :=
  pushout (-𝟙 A) S

/-- The endpoint maps of the biproduct of two extensions compose to zero. -/
theorem biprodExtension_zero (S T : Extension A B) :
    biprod.map S.f T.f ≫ biprod.map S.g T.g = 0 := sorry

/-- The short complex obtained by taking the biproduct of two extensions is short exact. -/
theorem biprodExtensionShortExact (S T : Extension A B) :
    (ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
      (biprodExtension_zero S T)).ShortExact := sorry

/-- The coordinatewise biproduct of two fixed-endpoint extensions. -/
@[stacks 010L "biproduct of fixed-endpoint extensions"]
noncomputable def biprodExtension (S T : Extension A B) : Extension (A ⊞ A) (B ⊞ B) :=
  Extension.mk
    (S.E ⊞ T.E)
    (biprod.map S.f T.f)
    (biprod.map S.g T.g)
    (biprodExtension_zero S T)
    (biprodExtensionShortExact S T)

/-- The Baer sum of two extensions, formed by a biproduct, pullback, and pushout. -/
@[stacks 010L "Baer sum of fixed-endpoint extensions"]
noncomputable def baerSum (S T : Extension A B) : Extension A B :=
  pushout (biprod.desc (𝟙 A) (𝟙 A))
    (pullback (biprod.lift (𝟙 B) (𝟙 B)) (biprodExtension S T))

/-- Isomorphisms of extensions are preserved by coordinatewise biproducts. -/
theorem isIsomorphic_biprodExtension {S₁ S₂ T₁ T₂ : Extension A B}
    (hS : IsIsomorphic S₁ S₂) (hT : IsIsomorphic T₁ T₂) :
    IsIsomorphic (biprodExtension S₁ T₁) (biprodExtension S₂ T₂) := sorry

/-- Isomorphisms of extensions are preserved by negation. -/
theorem isIsomorphic_neg (h : IsIsomorphic S T) : IsIsomorphic (neg S) (neg T) := sorry

/-- Isomorphisms of extensions are preserved by Baer sums. -/
theorem isIsomorphic_baerSum {S₁ S₂ T₁ T₂ : Extension A B}
    (hS : IsIsomorphic S₁ S₂) (hT : IsIsomorphic T₁ T₂) :
    IsIsomorphic (baerSum S₁ T₁) (baerSum S₂ T₂) := sorry

end Extension

namespace ExtensionClass

variable {A' B' : C}

/-- The class of the standard split extension. -/
@[stacks 010L "zero extension class"]
noncomputable def zero (A B : C) : ExtensionClass A B :=
  ⟦Extension.split A B⟧

/-- Negation on source-facing extension classes. -/
@[stacks 010L "negation of extension classes"]
noncomputable def neg : ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map Extension.neg fun _ _ h ↦ Extension.isIsomorphic_neg h

/-- The Baer sum on source-facing extension classes. -/
@[stacks 010L "Baer sum on extension classes"]
noncomputable def baerSum : ExtensionClass A B → ExtensionClass A B → ExtensionClass A B :=
  _root_.Quotient.map₂ Extension.baerSum fun _ _ h₁ _ _ h₂ ↦
    Extension.isIsomorphic_baerSum h₁ h₂

/-- The chosen zero extension class. -/
noncomputable instance : Zero (ExtensionClass A B) := ⟨zero A B⟩

/-- The chosen negation on extension classes. -/
noncomputable instance : Neg (ExtensionClass A B) := ⟨neg⟩

/-- The chosen Baer-sum addition on extension classes. -/
noncomputable instance : Add (ExtensionClass A B) := ⟨baerSum⟩

/-- Negation computes on a representative extension. -/
theorem neg_mk (S : Extension A B) :
    neg (⟦S⟧ : ExtensionClass A B) = ⟦Extension.neg S⟧ := sorry

/-- The Baer sum computes on representative extensions. -/
theorem baerSum_mk (S T : Extension A B) :
    baerSum (⟦S⟧ : ExtensionClass A B) ⟦T⟧ = ⟦Extension.baerSum S T⟧ := sorry

/-- Pullback preserves Baer sums of extension classes. -/
theorem pullback_baerSum (u : B' ⟶ B) (xi eta : ExtensionClass A B) :
    pullback u (baerSum xi eta) = baerSum (pullback u xi) (pullback u eta) := sorry

/-- Pushout preserves Baer sums of extension classes. -/
theorem pushout_baerSum (a : A ⟶ A') (xi eta : ExtensionClass A B) :
    pushout a (baerSum xi eta) = baerSum (pushout a xi) (pushout a eta) := sorry

/-- Pullback commutes with negation of extension classes. -/
theorem pullback_neg (u : B' ⟶ B) (xi : ExtensionClass A B) :
    pullback u (neg xi) = neg (pullback u xi) := sorry

/-- Pushout commutes with negation of extension classes. -/
theorem pushout_neg (a : A ⟶ A') (xi : ExtensionClass A B) :
    pushout a (neg xi) = neg (pushout a xi) := sorry

end ExtensionClass

end

end CategoryTheory
