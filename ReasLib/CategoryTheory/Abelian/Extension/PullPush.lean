/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Extension.Isomorphism

@[expose] public section

/-!
# Pullbacks and Pushouts of Fixed-Endpoint Extensions

This module gives concrete base-change constructions for short exact sequences with fixed
endpoints.  The constructions retain their chosen pullback and pushout middle objects, while the
quotient-level API records their invariant extension classes.
-/

namespace CategoryTheory

universe v u

open Limits

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : C}

namespace Extension

variable {S T : Extension A B}
variable {A' B' : C}

/-- The compatibility needed to define the canonical inclusion into a pullback extension. -/
theorem pullbackInclusion_condition (u : B' ⟶ B) (S : Extension A B) :
    (0 : A ⟶ B') ≫ u = S.f ≫ S.g := sorry

/-- The left map of the pullback extension. -/
noncomputable def pullbackInclusion (u : B' ⟶ B) (S : Extension A B) :
    A ⟶ Limits.pullback u S.g :=
  Limits.pullback.lift 0 S.f (pullbackInclusion_condition u S)

/-- The pullback extension's left map composes trivially with its right map. -/
@[simp] theorem pullbackInclusion_comp_fst (u : B' ⟶ B) (S : Extension A B) :
    pullbackInclusion u S ≫ Limits.pullback.fst u S.g = 0 := sorry

/-- The pullback inclusion recovers the original left map through the second projection. -/
@[simp] theorem pullbackInclusion_comp_snd (u : B' ⟶ B) (S : Extension A B) :
    pullbackInclusion u S ≫ Limits.pullback.snd u S.g = S.f := sorry

/-- The short complex defining a pullback extension is short exact. -/
theorem pullbackShortExact (u : B' ⟶ B) (S : Extension A B) :
    (ShortComplex.mk (pullbackInclusion u S) (Limits.pullback.fst u S.g)
      (pullbackInclusion_comp_fst u S)).ShortExact := sorry

/-- The compatibility needed to define the canonical projection out of a pushout extension. -/
theorem pushoutProjection_condition (a : A ⟶ A') (S : Extension A B) :
    a ≫ (0 : A' ⟶ B) = S.f ≫ S.g := sorry

/-- The right map of the pushout extension. -/
noncomputable def pushoutProjection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout a S.f ⟶ B :=
  Limits.pushout.desc (0 : A' ⟶ B) S.g (pushoutProjection_condition a S)

/-- The pushout extension's left map composes trivially with its right map. -/
@[simp] theorem pushoutInl_comp_projection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout.inl a S.f ≫ pushoutProjection a S = 0 := sorry

/-- The pushout projection recovers the original right map through the second inclusion. -/
@[simp] theorem pushoutInr_comp_projection (a : A ⟶ A') (S : Extension A B) :
    Limits.pushout.inr a S.f ≫ pushoutProjection a S = S.g := sorry

/-- The short complex defining a pushout extension is short exact. -/
theorem pushoutShortExact (a : A ⟶ A') (S : Extension A B) :
    (ShortComplex.mk (Limits.pushout.inl a S.f) (pushoutProjection a S)
      (pushoutInl_comp_projection a S)).ShortExact := sorry

/-- Pulling back an extension along its right endpoint. -/
@[stacks 010K "fixed-endpoint extension pullback"]
noncomputable def pullback (u : B' ⟶ B) (S : Extension A B) : Extension A B' :=
  Extension.mk
    (Limits.pullback u S.g)
    (pullbackInclusion u S)
    (Limits.pullback.fst u S.g)
    (pullbackInclusion_comp_fst u S)
    (pullbackShortExact u S)

/-- Pushing out an extension along its left endpoint. -/
@[stacks 010K "fixed-endpoint extension pushout"]
noncomputable def pushout (a : A ⟶ A') (S : Extension A B) : Extension A' B :=
  Extension.mk
    (Limits.pushout a S.f)
    (Limits.pushout.inl a S.f)
    (pushoutProjection a S)
    (pushoutInl_comp_projection a S)
    (pushoutShortExact a S)

/-- Isomorphisms of fixed-endpoint extensions are preserved by pullback. -/
theorem isIsomorphic_pullback (u : B' ⟶ B) (h : IsIsomorphic S T) :
    IsIsomorphic (pullback u S) (pullback u T) := sorry

/-- Isomorphisms of fixed-endpoint extensions are preserved by pushout. -/
theorem isIsomorphic_pushout (a : A ⟶ A') (h : IsIsomorphic S T) :
    IsIsomorphic (pushout a S) (pushout a T) := sorry

end Extension

namespace ExtensionClass

variable {A' A'' B' B'' : C}

/-- Pullback of extension classes along a morphism of right endpoints. -/
@[stacks 010K "extension-class pullback"]
noncomputable def pullback (u : B' ⟶ B) : ExtensionClass A B → ExtensionClass A B' :=
  _root_.Quotient.map (Extension.pullback u) fun _ _ h ↦ Extension.isIsomorphic_pullback u h

/-- Pushout of extension classes along a morphism of left endpoints. -/
@[stacks 010K "extension-class pushout"]
noncomputable def pushout (a : A ⟶ A') : ExtensionClass A B → ExtensionClass A' B :=
  _root_.Quotient.map (Extension.pushout a) fun _ _ h ↦ Extension.isIsomorphic_pushout a h

/-- Pullback on extension classes computes on a representative. -/
theorem pullback_mk (u : B' ⟶ B) (S : Extension A B) :
    pullback u (⟦S⟧ : ExtensionClass A B) = ⟦Extension.pullback u S⟧ := sorry

/-- Pushout on extension classes computes on a representative. -/
theorem pushout_mk (a : A ⟶ A') (S : Extension A B) :
    pushout a (⟦S⟧ : ExtensionClass A B) = ⟦Extension.pushout a S⟧ := sorry

/-- Pullback along the identity of the right endpoint is the identity on extension classes. -/
@[simp, stacks 010L "extension-class pullback identity"]
theorem pullback_id (xi : ExtensionClass A B) :
    pullback (𝟙 B) xi = xi := sorry

/-- Pushout along the identity of the left endpoint is the identity on extension classes. -/
@[simp, stacks 010L "extension-class pushout identity"]
theorem pushout_id (xi : ExtensionClass A B) :
    pushout (𝟙 A) xi = xi := sorry

/-- Pullback along a composite agrees with successive pullbacks on extension classes. -/
theorem pullback_comp (u : B' ⟶ B) (u' : B'' ⟶ B') (xi : ExtensionClass A B) :
    pullback u' (pullback u xi) = pullback (u' ≫ u) xi := sorry

/-- Pushout along a composite agrees with successive pushouts on extension classes. -/
theorem pushout_comp (a : A ⟶ A') (a' : A' ⟶ A'') (xi : ExtensionClass A B) :
    pushout a' (pushout a xi) = pushout (a ≫ a') xi := sorry

/-- Pullback and pushout on independent endpoints commute on extension classes. -/
theorem pullback_pushout (u : B' ⟶ B) (a : A ⟶ A') (xi : ExtensionClass A B) :
    pullback u (pushout a xi) = pushout a (pullback u xi) := sorry

end ExtensionClass

end

end CategoryTheory
