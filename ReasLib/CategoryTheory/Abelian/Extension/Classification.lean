module

public import ReasLib.CategoryTheory.Abelian.Extension.Ext

@[expose] public section

/-!
# Classification of Fixed-Endpoint Extensions

@stack 010L
@stack 0AUL

This module transports the canonical additive structure on `Ext B A 1` to source-facing fixed-
endpoint extension classes.  It also packages pullback and pushout as additive maps between the
resulting extension groups.
-/

namespace CategoryTheory

universe w v u

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

namespace ExtensionClass

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' A'' B B' B'' : C}

/-- Subtraction of source-facing extension classes, induced by Baer sum and negation. -/
@[stacks 010L "subtraction of extension classes", instance]
noncomputable instance : Sub (ExtensionClass A B) where
  sub xi eta := xi + -eta

/-- Natural-number scalar multiplication of extension classes by repeated Baer sum. -/
@[stacks 010L "natural-number scalar multiplication of extension classes", instance]
noncomputable instance : SMul ℕ (ExtensionClass A B) where
  smul n xi := nsmulRec n xi

/-- Integer scalar multiplication of extension classes by repeated Baer sum and negation. -/
@[stacks 010L "integer scalar multiplication of extension classes", instance]
noncomputable instance : SMul ℤ (ExtensionClass A B) where
  smul := zsmulRec nsmulRec

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {A A' B B' : C}

/-- The canonical `Ext¹` bridge preserves subtraction of extension classes. -/
@[simp] theorem toExt_sub (xi eta : ExtensionClass A B) :
    toExt (xi - eta) = toExt xi - toExt eta := sorry

/-- The canonical `Ext¹` bridge preserves natural-number scalar multiplication. -/
@[simp] theorem toExt_nsmul (xi : ExtensionClass A B) (n : ℕ) :
    toExt (n • xi) = n • toExt xi := sorry

/-- The canonical `Ext¹` bridge preserves integer scalar multiplication. -/
@[simp] theorem toExt_zsmul (xi : ExtensionClass A B) (n : ℤ) :
    toExt (n • xi) = n • toExt xi := sorry

/-- The canonical comparison from source-facing extension classes to `Ext¹` is bijective. -/
@[stacks 010L, stacks 0AUL "extension classes classify Ext-one"]
theorem toExt_bijective :
    Function.Bijective (toExt : ExtensionClass A B → Ext B A 1) := sorry

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A A' B B' : C}

/-- Lemma 12.6.3: Baer sum gives source-facing extension classes a commutative group law. -/
@[stacks 010L]
noncomputable instance : AddCommGroup (ExtensionClass A B) :=
  -- Local instance justification (defeq pin): `HasExt.standard C` fixes the
  -- universe-polymorphic standard `Ext` structure used to establish the group-law fields.
  -- The zero, negation, and Baer-sum data were fixed before this instance.
  letI : HasExt.{max u v} C := HasExt.standard C
  Function.Injective.addCommGroup toExt toExt_bijective.injective toExt_zero toExt_add toExt_neg
    toExt_sub toExt_nsmul toExt_zsmul

section

variable [HasExt.{w} C]

/-- The canonical additive map from source-facing extension classes to `Ext¹(B, A)`.

The inverse is not selected from `toExt_bijective`: while that theorem is deferred, selecting an
inverse would make its proof debt part of concrete data. -/
@[stacks 010L, stacks 0AUL "additive extension-class comparison with Ext-one"]
noncomputable def toExtAddHom : ExtensionClass A B →+ Ext B A 1 where
  toFun := toExt
  map_zero' := toExt_zero
  map_add' := toExt_add

/-- The forward additive comparison computes as the canonical `Ext¹` bridge. -/
@[simp] theorem toExtAddHom_apply (xi : ExtensionClass A B) :
    toExtAddHom xi = toExt xi := sorry

end

/-- Pullback sends the zero extension class to zero. -/
@[simp] theorem pullback_zero (u : B' ⟶ B) :
    pullback u (0 : ExtensionClass A B) = 0 := sorry

/-- Pullback preserves addition of extension classes. -/
@[simp] theorem pullback_add (u : B' ⟶ B) (xi eta : ExtensionClass A B) :
    pullback u (xi + eta) = pullback u xi + pullback u eta := sorry

/-- Pullback preserves subtraction of extension classes. -/
@[simp] theorem pullback_sub (u : B' ⟶ B) (xi eta : ExtensionClass A B) :
    pullback u (xi - eta) = pullback u xi - pullback u eta := sorry

/-- Pushout sends the zero extension class to zero. -/
@[simp] theorem pushout_zero (a : A ⟶ A') :
    pushout a (0 : ExtensionClass A B) = 0 := sorry

/-- Pushout preserves addition of extension classes. -/
@[simp] theorem pushout_add (a : A ⟶ A') (xi eta : ExtensionClass A B) :
    pushout a (xi + eta) = pushout a xi + pushout a eta := sorry

/-- Pushout preserves subtraction of extension classes. -/
@[simp] theorem pushout_sub (a : A ⟶ A') (xi eta : ExtensionClass A B) :
    pushout a (xi - eta) = pushout a xi - pushout a eta := sorry

/-- Pullback of extension classes, packaged as an additive homomorphism in the right endpoint. -/
@[stacks 010L "additive pullback of extension classes"]
noncomputable def pullbackAddHom (u : B' ⟶ B) : ExtensionClass A B →+ ExtensionClass A B' where
  toFun := pullback u
  map_zero' := pullback_zero u
  map_add' := pullback_add u

/-- Pushout of extension classes, packaged as an additive homomorphism in the left endpoint. -/
@[stacks 010L "additive pushout of extension classes"]
noncomputable def pushoutAddHom (a : A ⟶ A') : ExtensionClass A B →+ ExtensionClass A' B where
  toFun := pushout a
  map_zero' := pushout_zero a
  map_add' := pushout_add a

/-- The additive pullback homomorphism computes as the quotient-level pullback. -/
@[simp] theorem pullbackAddHom_apply (u : B' ⟶ B) (xi : ExtensionClass A B) :
    pullbackAddHom u xi = pullback u xi := sorry

/-- The additive pushout homomorphism computes as the quotient-level pushout. -/
@[simp] theorem pushoutAddHom_apply (a : A ⟶ A') (xi : ExtensionClass A B) :
    pushoutAddHom a xi = pushout a xi := sorry

/-- Additive pullback along the identity right-endpoint map is the identity homomorphism. -/
@[simp, stacks 010L "additive extension-class pullback identity"]
theorem pullbackAddHom_id :
    pullbackAddHom (𝟙 B) = AddMonoidHom.id (ExtensionClass A B) := sorry

/-- Additive pullback along an identity is the identity morphism in `AddCommGrpCat`. -/
@[simp, stacks 010L "categorified additive extension-class pullback identity"]
theorem pullbackAddHom_map_id :
    AddCommGrpCat.ofHom (pullbackAddHom (A := A) (𝟙 B)) =
      𝟙 (AddCommGrpCat.of (ExtensionClass A B)) := sorry

/-- Additive pullback is compatible with composition of right-endpoint maps. -/
@[stacks 010L "additive extension-class pullback composition"]
theorem pullbackAddHom_comp (u : B' ⟶ B) (u' : B'' ⟶ B') :
    (pullbackAddHom (A := A) u').comp (pullbackAddHom (A := A) u) =
      pullbackAddHom (A := A) (u' ≫ u) := sorry

/-- Additive pushout along the identity left-endpoint map is the identity homomorphism. -/
@[simp, stacks 010L "additive extension-class pushout identity"]
theorem pushoutAddHom_id :
    pushoutAddHom (𝟙 A) = AddMonoidHom.id (ExtensionClass A B) := sorry

/-- Additive pushout along an identity is the identity morphism in `AddCommGrpCat`. -/
@[simp, stacks 010L "categorified additive extension-class pushout identity"]
theorem pushoutAddHom_map_id :
    AddCommGrpCat.ofHom (pushoutAddHom (B := B) (𝟙 A)) =
      𝟙 (AddCommGrpCat.of (ExtensionClass A B)) := sorry

/-- Additive pushout is compatible with composition of left-endpoint maps. -/
@[stacks 010L "additive extension-class pushout composition"]
theorem pushoutAddHom_comp (a : A ⟶ A') (a' : A' ⟶ A'') :
    (pushoutAddHom (B := B) a').comp (pushoutAddHom (B := B) a) =
      pushoutAddHom (B := B) (a ≫ a') := sorry

/-- Additive pullback and pushout on independent endpoints commute. -/
@[stacks 010L "commuting additive extension-class base changes"]
theorem pullback_pushout_addHom (u : B' ⟶ B) (a : A ⟶ A') :
    (pullbackAddHom u).comp (pushoutAddHom a) =
      (pushoutAddHom a).comp (pullbackAddHom u) := sorry

/-- Additive pushout composition expressed as a morphism equality in `AddCommGrpCat`. -/
@[stacks 010L "categorified additive extension-class pushout composition"]
theorem pushoutAddHom_map_comp (a : A ⟶ A') (a' : A' ⟶ A'') :
    AddCommGrpCat.ofHom (pushoutAddHom (B := B) (a ≫ a')) =
      AddCommGrpCat.ofHom (pushoutAddHom (B := B) a) ≫
        AddCommGrpCat.ofHom (pushoutAddHom (B := B) a') := sorry

/-- Additive pullback composition expressed as a morphism equality in `AddCommGrpCat`. -/
@[stacks 010L "categorified additive extension-class pullback composition"]
theorem pullbackAddHom_map_comp (u : B' ⟶ B) (u' : B'' ⟶ B') :
    AddCommGrpCat.ofHom (pullbackAddHom (A := A) (u' ≫ u)) =
      AddCommGrpCat.ofHom (pullbackAddHom (A := A) u) ≫
        AddCommGrpCat.ofHom (pullbackAddHom (A := A) u') := sorry

/-- The two endpoint actions satisfy the naturality square in `AddCommGrpCat`. -/
@[stacks 010L "extension-class base-change naturality"]
theorem baseChange_naturality (u : B' ⟶ B) (a : A ⟶ A') :
    AddCommGrpCat.ofHom (pushoutAddHom (B := B) a) ≫
        AddCommGrpCat.ofHom (pullbackAddHom (A := A') u) =
      AddCommGrpCat.ofHom (pullbackAddHom (A := A) u) ≫
        AddCommGrpCat.ofHom (pushoutAddHom (B := B') a) := sorry

/-- The covariant extension-class functor in the left endpoint with right endpoint `B` fixed. -/
@[stacks 010L "fixed-right-endpoint extension-class functor"]
noncomputable def functorObj (B : C) : C ⥤ AddCommGrpCat.{max u v} where
  obj A := AddCommGrpCat.of (ExtensionClass A B)
  map a := AddCommGrpCat.ofHom (pushoutAddHom (B := B) a)
  map_id A := pushoutAddHom_map_id (A := A) (B := B)
  map_comp a a' := pushoutAddHom_map_comp (B := B) a a'

/-- The base-change square written using the fixed-right-endpoint extension-class functors. -/
@[stacks 010L "extension-class pullback naturality"]
theorem pullbackNatTrans_naturality (u : B' ⟶ B) (a : A ⟶ A') :
    (functorObj B).map a ≫ AddCommGrpCat.ofHom (pullbackAddHom (A := A') u) =
      AddCommGrpCat.ofHom (pullbackAddHom (A := A) u) ≫ (functorObj B').map a := sorry

/-- Pullback in the right endpoint, packaged as a natural transformation of extension-class
functors. -/
@[stacks 010L "extension-class pullback natural transformation"]
noncomputable def pullbackNatTrans (u : B' ⟶ B) : functorObj B ⟶ functorObj B' where
  app A := AddCommGrpCat.ofHom (pullbackAddHom (A := A) u)
  naturality := fun {X Y} f ↦
    pullbackNatTrans_naturality (A := X) (A' := Y) u f

/-- Pullback along an identity is the identity natural transformation of fixed-right-endpoint
extension-class functors. -/
@[simp, stacks 010L "extension-class pullback natural transformation identity"]
theorem pullbackNatTrans_id (B : C) :
    pullbackNatTrans (𝟙 B) = 𝟙 (functorObj B) := sorry

/-- Pullback natural transformations compose with the right-endpoint maps. -/
@[stacks 010L "extension-class pullback natural transformation composition"]
theorem pullbackNatTrans_comp (u : B' ⟶ B) (u' : B'' ⟶ B') :
    pullbackNatTrans (u' ≫ u) = pullbackNatTrans u ≫ pullbackNatTrans u' := sorry

/-- The source-facing extension-class bifunctor, contravariant in the right endpoint and
covariant in the left endpoint. -/
@[stacks 010L "extension-class bifunctor"]
noncomputable def functor : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{max u v} where
  obj B := functorObj B.unop
  map f := pullbackNatTrans f.unop
  map_id B := pullbackNatTrans_id B.unop
  map_comp f f' := pullbackNatTrans_comp f.unop f'.unop

section

variable [HasExt.{max u v} C]

namespace toExt

/-- The forward `Ext¹` bridge is natural in the left endpoint. -/
@[stacks 010L "Ext-one bridge pushout naturality"]
theorem addHom_pushout (a : A ⟶ A') :
    AddCommGrpCat.ofHom (pushoutAddHom (B := B) a) ≫
        AddCommGrpCat.ofHom (toExtAddHom (A := A') (B := B)) =
      AddCommGrpCat.ofHom (toExtAddHom (A := A) (B := B)) ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp B (add_zero 1)) := sorry

/-- The forward `Ext¹` bridge for a fixed right endpoint, packaged as a natural transformation. -/
@[stacks 010L "fixed-right-endpoint Ext-one bridge"]
noncomputable def natTransObj (B : C) : functorObj B ⟶ Abelian.extFunctorObj B 1 where
  app A := AddCommGrpCat.ofHom (toExtAddHom (A := A) (B := B))
  naturality := fun {X Y} f ↦
    addHom_pushout (A := X) (A' := Y) (B := B) f

/-- The fixed-right-endpoint forward `Ext¹` bridges are natural under pullback. -/
@[stacks 010L "Ext-one bridge pullback naturality"]
theorem natTransObj_naturality {B B' : Cᵒᵖ} (f : B ⟶ B') :
    pullbackNatTrans f.unop ≫ natTransObj B'.unop =
      natTransObj B.unop ≫ (Abelian.extFunctor (C := C) 1).map f := sorry

/-- The canonical forward natural transformation from extension classes to Mathlib's
degree-one `Ext` bifunctor. -/
@[stacks 010L "extension-class to Ext-one natural transformation"]
noncomputable def natTrans : functor ⟶ Abelian.extFunctor (C := C) 1 where
  app B := natTransObj B.unop
  naturality := fun {X Y} f ↦ natTransObj_naturality (B := X) (B' := Y) f

end toExt

end

end

end ExtensionClass

end CategoryTheory
