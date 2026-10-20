/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Finite
public import ReasLib.Algebra.Category.ModuleCat.Product
public import ReasLib.Algebra.Module.Product.Finite
public import ReasLib.CategoryTheory.ObjectProperty.Product

/-!
# Finite Modules over Product Rings

This file lifts the idempotent factorization and projection embeddings of modules over a product
ring to the full subcategories of finitely generated modules.  It is independent of
Grothendieck groups and can therefore support any construction on finite modules.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ModuleCat.Product.Finite

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The heterogeneous product category instance for finitely generated module categories over
rings in independent universes. -/
local instance heterogeneousFGModuleCategory :
    Category.{w} (FGModuleCat.{w} R × FGModuleCat.{w} S) :=
  CategoryTheory.prod' (FGModuleCat.{w} R) (FGModuleCat.{w} S)

/-- The left idempotent factor of a finite product-ring module is finite. -/
@[stacks 00JH "finite product ring left factor"]
theorem left_mem (M : ModuleCat.{w} (R × S)) (hM : ModuleCat.isFG.{w} (R × S) M) :
    ModuleCat.isFG.{w} R (ModuleCat.Product.left R S M) :=
  (Module.Product.finite_iff R S M).mp hM |>.1

/-- The right idempotent factor of a finite product-ring module is finite. -/
@[stacks 00JH "finite product ring right factor"]
theorem right_mem (M : ModuleCat.{w} (R × S)) (hM : ModuleCat.isFG.{w} (R × S) M) :
    ModuleCat.isFG.{w} S (ModuleCat.Product.right R S M) :=
  (Module.Product.finite_iff R S M).mp hM |>.2

/-- The first-projection embedding preserves finite modules. -/
@[stacks 00JH "finite product ring left embedding"]
theorem leftEmbed_mem (M : ModuleCat.{w} R) (hM : ModuleCat.isFG.{w} R M) :
    ModuleCat.isFG.{w} (R × S) ((ModuleCat.Product.leftEmbed R S).obj M) := by
  apply (Module.Product.finite_iff R S ((ModuleCat.Product.leftEmbed R S).obj M)).2
  refine ⟨(ModuleCat.isFG R).prop_of_iso
    (ModuleCat.Product.LeftEmbed.leftIso R S M).symm hM, ?_⟩
  letI : Subsingleton
      (ModuleCat.Product.right R S ((ModuleCat.Product.leftEmbed R S).obj M)) :=
    ModuleCat.Product.LeftEmbed.right_subsingleton R S M
  exact ModuleCat.isFG_of_subsingleton S
    (ModuleCat.Product.right R S ((ModuleCat.Product.leftEmbed R S).obj M))

/-- The second-projection embedding preserves finite modules. -/
@[stacks 00JH "finite product ring right embedding"]
theorem rightEmbed_mem (M : ModuleCat.{w} S) (hM : ModuleCat.isFG.{w} S M) :
    ModuleCat.isFG.{w} (R × S) ((ModuleCat.Product.rightEmbed R S).obj M) := by
  apply (Module.Product.finite_iff R S ((ModuleCat.Product.rightEmbed R S).obj M)).2
  refine ⟨?_, (ModuleCat.isFG S).prop_of_iso
    (ModuleCat.Product.RightEmbed.rightIso R S M).symm hM⟩
  letI : Subsingleton
      (ModuleCat.Product.left R S ((ModuleCat.Product.rightEmbed R S).obj M)) :=
    ModuleCat.Product.RightEmbed.left_subsingleton R S M
  exact ModuleCat.isFG_of_subsingleton R
    (ModuleCat.Product.left R S ((ModuleCat.Product.rightEmbed R S).obj M))

/-- Combining finite modules over the two factors yields a finite module over the product ring. -/
@[stacks 00JH "finite product ring combination"]
theorem combine_mem (M : ModuleCat.{w} R) (N : ModuleCat.{w} S)
    (hM : ModuleCat.isFG.{w} R M) (hN : ModuleCat.isFG.{w} S N) :
    ModuleCat.isFG.{w} (R × S) (ModuleCat.Product.combineObj R S M N) := by
  apply (Module.Product.finite_iff R S (ModuleCat.Product.combineObj R S M N)).2
  exact ⟨(ModuleCat.isFG R).prop_of_iso (ModuleCat.Product.leftCombineIso R S M N).symm hM,
    (ModuleCat.isFG S).prop_of_iso (ModuleCat.Product.rightCombineIso R S M N).symm hN⟩

/-- A bundled module over a product ring is finitely generated exactly when its two idempotent
factors are finitely generated. -/
@[stacks 00JH "finite product ring module criterion"]
theorem isFG_iff (M : ModuleCat.{w} (R × S)) :
    ModuleCat.isFG.{w} (R × S) M ↔
      ModuleCat.isFG.{w} R (ModuleCat.Product.left R S M) ∧
        ModuleCat.isFG.{w} S (ModuleCat.Product.right R S M) :=
  Module.Product.finite_iff R S M

/-- Under the product-ring factor functor, finite generation is exactly the product of the two
factor finite-generation properties. -/
@[stacks 00JH "finite product ring factor property"]
theorem factor_property :
    ((ModuleCat.isFG.{w} R).prod (ModuleCat.isFG.{w} S)).inverseImage
        (ModuleCat.Product.factor R S) = ModuleCat.isFG.{w} (R × S) := by
  apply (ObjectProperty.inverseImage_prod_eq_iff _ _ _ _).2
  exact isFG_iff R S

/-- The canonical equivalence between finite modules over `R × S` and pairs of finite modules,
obtained by restricting the ambient module-category equivalence through the product object
property. -/
@[stacks 00JH "finite product ring category equivalence"]
def equivalence : FGModuleCat.{w} (R × S) ≌ FGModuleCat.{w} R × FGModuleCat.{w} S :=
  (ModuleCat.Product.equivalence R S).restrictProd (factor_property R S)

/-- The product-ring factorization functor on finitely generated modules. -/
@[stacks 00JH "finite product ring factor functor"]
def factor : FGModuleCat.{w} (R × S) ⥤ FGModuleCat.{w} R × FGModuleCat.{w} S :=
  (equivalence R S).functor

/-- The combination functor restricted to finitely generated modules. -/
@[stacks 00JH "finite product ring combination functor"]
def combine : FGModuleCat.{w} R × FGModuleCat.{w} S ⥤ FGModuleCat.{w} (R × S) :=
  (equivalence R S).inverse

/-- The left-factor functor restricted to finitely generated modules. -/
@[stacks 00JH "finite product ring left factor functor"]
def leftFunctor : FGModuleCat.{w} (R × S) ⥤ FGModuleCat.{w} R :=
  factor R S ⋙ CategoryTheory.Prod.fst (FGModuleCat.{w} R) (FGModuleCat.{w} S)

/-- The right-factor functor restricted to finitely generated modules. -/
@[stacks 00JH "finite product ring right factor functor"]
def rightFunctor : FGModuleCat.{w} (R × S) ⥤ FGModuleCat.{w} S :=
  factor R S ⋙ CategoryTheory.Prod.snd (FGModuleCat.{w} R) (FGModuleCat.{w} S)

/-- The left idempotent factor of a finite product-ring module as a finite module. -/
@[stacks 00JH "finite product ring left factor object"]
abbrev left (M : FGModuleCat.{w} (R × S)) : FGModuleCat.{w} R :=
  (leftFunctor R S).obj M

/-- The right idempotent factor of a finite product-ring module as a finite module. -/
@[stacks 00JH "finite product ring right factor object"]
abbrev right (M : FGModuleCat.{w} (R × S)) : FGModuleCat.{w} S :=
  (rightFunctor R S).obj M

/-- The underlying module of the finite left factor is the raw idempotent factor. -/
@[simp]
theorem left_obj (M : FGModuleCat.{w} (R × S)) :
    (left R S M).obj = ModuleCat.Product.left R S M.obj := rfl

/-- The underlying module of the finite right factor is the raw idempotent factor. -/
@[simp]
theorem right_obj (M : FGModuleCat.{w} (R × S)) :
    (right R S M).obj = ModuleCat.Product.right R S M.obj := rfl

/-- The first-projection embedding restricted to finitely generated modules. -/
@[stacks 00JH "finite product ring left module embedding"]
def leftEmbed : FGModuleCat.{w} R ⥤ FGModuleCat.{w} (R × S) :=
  ObjectProperty.lift (ModuleCat.isFG (R × S))
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.Product.leftEmbed R S)
    (fun M ↦ leftEmbed_mem R S M.obj M.property)

/-- The second-projection embedding restricted to finitely generated modules. -/
@[stacks 00JH "finite product ring right module embedding"]
def rightEmbed : FGModuleCat.{w} S ⥤ FGModuleCat.{w} (R × S) :=
  ObjectProperty.lift (ModuleCat.isFG (R × S))
    ((ModuleCat.isFG S).ι ⋙ ModuleCat.Product.rightEmbed R S)
    (fun M ↦ rightEmbed_mem R S M.obj M.property)

/-- The finite factorization isomorphism lifted from product-ring modules. -/
@[stacks 00JH "finite product ring factor combination isomorphism"]
def factorCombineIso (M : FGModuleCat.{w} (R × S)) :
    M ≅ (combine R S).obj ((factor R S).obj M) :=
  (equivalence R S).unitIso.app M

/-- The finite combination-factorization isomorphism lifted from product-ring modules. -/
@[stacks 00JH "finite product ring combination factor isomorphism"]
def combineFactorIso (X : FGModuleCat.{w} R × FGModuleCat.{w} S) :
    (combine R S ⋙ factor R S).obj X ≅ X :=
  (equivalence R S).counitIso.app X

/-- The unit isomorphism for the product-ring equivalence on finite modules. -/
@[stacks 00JH "finite product ring equivalence unit"]
def unitIso : 𝟭 (FGModuleCat.{w} (R × S)) ≅ factor R S ⋙ combine R S :=
  (equivalence R S).unitIso

/-- The counit isomorphism for the product-ring equivalence on finite modules. -/
@[stacks 00JH "finite product ring equivalence counit"]
def counitIso : combine R S ⋙ factor R S ≅ 𝟭 (FGModuleCat.{w} R × FGModuleCat.{w} S) :=
  (equivalence R S).counitIso

/-- The finite factorization functor is an equivalence. -/
@[stacks 00JH "finite product ring factor functor equivalence"]
instance factor_isEquivalence : (factor R S).IsEquivalence :=
  (equivalence R S).isEquivalence_functor

/-- The finite combination functor is an equivalence. -/
@[stacks 00JH "finite product ring combination functor equivalence"]
instance combine_isEquivalence : (combine R S).IsEquivalence :=
  (equivalence R S).isEquivalence_inverse

end CategoryTheory.ModuleCat.Product.Finite
