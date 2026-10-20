/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Category.ModuleCat.Product
public import ReasLib.RingTheory.Finiteness.Projective.Product
public import ReasLib.CategoryTheory.ObjectProperty.Product

/-!
# Finite Projective Modules over Product Rings

This file lifts the product-ring factorization and projection embeddings to finite-projective
modules.  It is independent of Grothendieck groups and is the common categorical input for
algebraic K-theory and derived-category applications.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ModuleCat.Product.FiniteProjective

variable (R : Type u) (S : Type v) [Ring R] [Ring S]

/-- The heterogeneous product category instance for finite-projective module categories over
rings in independent universes. -/
local instance heterogeneousFiniteProjectiveCategory :
    Category.{w} (ModuleCat.FiniteProjective.{u, w} R ×
      ModuleCat.FiniteProjective.{v, w} S) :=
  CategoryTheory.prod' (ModuleCat.FiniteProjective.{u, w} R)
    (ModuleCat.FiniteProjective.{v, w} S)

/-- The left idempotent factor of a finite-projective product-ring module is finite projective.
-/
@[stacks 00JH "finite projective product ring left factor"]
theorem left_mem (M : ModuleCat.{w} (R × S))
    (hM : ModuleCat.finiteProjective.{max u v, w} (R × S) M) :
    ModuleCat.finiteProjective.{u, w} R (ModuleCat.Product.left R S M) :=
  (Module.FiniteProjective.product_iff R S M).mp hM |>.1

/-- The right idempotent factor of a finite-projective product-ring module is finite projective.
-/
@[stacks 00JH "finite projective product ring right factor"]
theorem right_mem (M : ModuleCat.{w} (R × S))
    (hM : ModuleCat.finiteProjective.{max u v, w} (R × S) M) :
    ModuleCat.finiteProjective.{v, w} S (ModuleCat.Product.right R S M) :=
  (Module.FiniteProjective.product_iff R S M).mp hM |>.2

/-- The first-projection embedding preserves finite-projective modules. -/
@[stacks 00JH "finite projective product ring left embedding"]
theorem leftEmbed_mem (M : ModuleCat.{w} R)
    (hM : ModuleCat.finiteProjective.{u, w} R M) :
    ModuleCat.finiteProjective.{max u v, w} (R × S)
      ((ModuleCat.Product.leftEmbed R S).obj M) := by
  apply (Module.FiniteProjective.product_iff R S
    ((ModuleCat.Product.leftEmbed R S).obj M)).2
  refine ⟨(ModuleCat.finiteProjective R).prop_of_iso
    (ModuleCat.Product.LeftEmbed.leftIso R S M).symm hM, ?_⟩
  letI : Subsingleton
      (ModuleCat.Product.right R S ((ModuleCat.Product.leftEmbed R S).obj M)) :=
    ModuleCat.Product.LeftEmbed.right_subsingleton R S M
  exact ModuleCat.finiteProjective_of_subsingleton S
    (ModuleCat.Product.right R S ((ModuleCat.Product.leftEmbed R S).obj M))

/-- The second-projection embedding preserves finite-projective modules. -/
@[stacks 00JH "finite projective product ring right embedding"]
theorem rightEmbed_mem (M : ModuleCat.{w} S)
    (hM : ModuleCat.finiteProjective.{v, w} S M) :
    ModuleCat.finiteProjective.{max u v, w} (R × S)
      ((ModuleCat.Product.rightEmbed R S).obj M) := by
  apply (Module.FiniteProjective.product_iff R S
    ((ModuleCat.Product.rightEmbed R S).obj M)).2
  refine ⟨?_, (ModuleCat.finiteProjective S).prop_of_iso
    (ModuleCat.Product.RightEmbed.rightIso R S M).symm hM⟩
  letI : Subsingleton
      (ModuleCat.Product.left R S ((ModuleCat.Product.rightEmbed R S).obj M)) :=
    ModuleCat.Product.RightEmbed.left_subsingleton R S M
  exact ModuleCat.finiteProjective_of_subsingleton R
    (ModuleCat.Product.left R S ((ModuleCat.Product.rightEmbed R S).obj M))

/-- Combining finite-projective modules over the two factors gives a finite-projective module
over the product ring. -/
@[stacks 00JH "finite projective product ring combination"]
theorem combine_mem (M : ModuleCat.{w} R) (N : ModuleCat.{w} S)
    (hM : ModuleCat.finiteProjective.{u, w} R M)
    (hN : ModuleCat.finiteProjective.{v, w} S N) :
    ModuleCat.finiteProjective.{max u v, w} (R × S)
      (ModuleCat.Product.combineObj R S M N) := by
  apply (Module.FiniteProjective.product_iff R S
    (ModuleCat.Product.combineObj R S M N)).2
  exact ⟨(ModuleCat.finiteProjective R).prop_of_iso
      (ModuleCat.Product.leftCombineIso R S M N).symm hM,
    (ModuleCat.finiteProjective S).prop_of_iso
      (ModuleCat.Product.rightCombineIso R S M N).symm hN⟩

/-- A bundled module over a product ring is finite projective exactly when its two idempotent
factors are finite projective. -/
@[stacks 00JH "finite projective product ring module criterion"]
theorem finiteProjective_iff (M : ModuleCat.{w} (R × S)) :
    ModuleCat.finiteProjective.{max u v, w} (R × S) M ↔
      ModuleCat.finiteProjective.{u, w} R (ModuleCat.Product.left R S M) ∧
        ModuleCat.finiteProjective.{v, w} S (ModuleCat.Product.right R S M) :=
  Module.FiniteProjective.product_iff R S M

/-- Under the product-ring factor functor, finite projectivity is exactly the product of the two
factor finite-projective properties. -/
@[stacks 00JH "finite projective product ring factor property"]
theorem factor_property :
    ((ModuleCat.finiteProjective.{u, w} R).prod (ModuleCat.finiteProjective.{v, w} S)).inverseImage
        (ModuleCat.Product.factor R S) = ModuleCat.finiteProjective.{max u v, w} (R × S) := by
  apply (ObjectProperty.inverseImage_prod_eq_iff _ _ _ _).2
  exact finiteProjective_iff R S

/-- The canonical equivalence between finite-projective modules over `R × S` and pairs of
finite-projective modules, obtained by restricting the ambient module-category equivalence
through the product object property. -/
@[stacks 00JH "finite projective product ring category equivalence"]
def equivalence : ModuleCat.FiniteProjective.{max u v, w} (R × S) ≌
    ModuleCat.FiniteProjective.{u, w} R × ModuleCat.FiniteProjective.{v, w} S :=
  (ModuleCat.Product.equivalence R S).restrictProd (factor_property R S)

/-- The product-ring factorization functor on finite-projective modules. -/
@[stacks 00JH "finite projective product ring factor functor"]
def factor : ModuleCat.FiniteProjective.{max u v, w} (R × S) ⥤
    ModuleCat.FiniteProjective.{u, w} R × ModuleCat.FiniteProjective.{v, w} S :=
  (equivalence R S).functor

/-- The combination functor restricted to finite-projective modules. -/
@[stacks 00JH "finite projective product ring combination functor"]
def combine : ModuleCat.FiniteProjective.{u, w} R × ModuleCat.FiniteProjective.{v, w} S ⥤
    ModuleCat.FiniteProjective.{max u v, w} (R × S) :=
  (equivalence R S).inverse

/-- The left-factor functor restricted to finite-projective modules. -/
@[stacks 00JH "finite projective product ring left factor functor"]
def leftFunctor : ModuleCat.FiniteProjective.{max u v, w} (R × S) ⥤
    ModuleCat.FiniteProjective.{u, w} R :=
  factor R S ⋙ CategoryTheory.Prod.fst (ModuleCat.FiniteProjective.{u, w} R)
    (ModuleCat.FiniteProjective.{v, w} S)

/-- The right-factor functor restricted to finite-projective modules. -/
@[stacks 00JH "finite projective product ring right factor functor"]
def rightFunctor : ModuleCat.FiniteProjective.{max u v, w} (R × S) ⥤
    ModuleCat.FiniteProjective.{v, w} S :=
  factor R S ⋙ CategoryTheory.Prod.snd (ModuleCat.FiniteProjective.{u, w} R)
    (ModuleCat.FiniteProjective.{v, w} S)

/-- The left idempotent factor of a finite-projective product-ring module. -/
@[stacks 00JH "finite projective product ring left factor object"]
abbrev left (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    ModuleCat.FiniteProjective.{u, w} R :=
  (leftFunctor R S).obj M

/-- The right idempotent factor of a finite-projective product-ring module. -/
@[stacks 00JH "finite projective product ring right factor object"]
abbrev right (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    ModuleCat.FiniteProjective.{v, w} S :=
  (rightFunctor R S).obj M

/-- The underlying module of the finite-projective left factor is the raw idempotent factor. -/
@[simp]
theorem left_obj (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    (left R S M).obj = ModuleCat.Product.left R S M.obj := rfl

/-- The underlying module of the finite-projective right factor is the raw idempotent factor. -/
@[simp]
theorem right_obj (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    (right R S M).obj = ModuleCat.Product.right R S M.obj := rfl

/-- The first-projection embedding restricted to finite-projective modules. -/
@[stacks 00JH "finite projective product ring left module embedding"]
def leftEmbed : ModuleCat.FiniteProjective.{u, w} R ⥤
    ModuleCat.FiniteProjective.{max u v, w} (R × S) :=
  ObjectProperty.lift (ModuleCat.finiteProjective (R × S))
    ((ModuleCat.finiteProjective R).ι ⋙ ModuleCat.Product.leftEmbed R S)
    (fun M ↦ leftEmbed_mem R S M.obj M.property)

/-- The second-projection embedding restricted to finite-projective modules. -/
@[stacks 00JH "finite projective product ring right module embedding"]
def rightEmbed : ModuleCat.FiniteProjective.{v, w} S ⥤
    ModuleCat.FiniteProjective.{max u v, w} (R × S) :=
  ObjectProperty.lift (ModuleCat.finiteProjective (R × S))
    ((ModuleCat.finiteProjective S).ι ⋙ ModuleCat.Product.rightEmbed R S)
    (fun M ↦ rightEmbed_mem R S M.obj M.property)

/-- The finite-projective factorization isomorphism lifted from product-ring modules. -/
@[stacks 00JH "finite projective product ring factor combination isomorphism"]
def factorCombineIso (M : ModuleCat.FiniteProjective.{max u v, w} (R × S)) :
    M ≅ (combine R S).obj ((factor R S).obj M) :=
  (equivalence R S).unitIso.app M

/-- The finite-projective combination-factorization isomorphism lifted from product-ring modules.
-/
@[stacks 00JH "finite projective product ring combination factor isomorphism"]
def combineFactorIso (X : ModuleCat.FiniteProjective.{u, w} R ×
    ModuleCat.FiniteProjective.{v, w} S) :
    (combine R S ⋙ factor R S).obj X ≅ X :=
  (equivalence R S).counitIso.app X

/-- The unit isomorphism for the product-ring equivalence on finite-projective modules. -/
@[stacks 00JH "finite projective product ring equivalence unit"]
def unitIso : 𝟭 (ModuleCat.FiniteProjective.{max u v, w} (R × S)) ≅
    factor R S ⋙ combine R S :=
  (equivalence R S).unitIso

/-- The counit isomorphism for the product-ring equivalence on finite-projective modules. -/
@[stacks 00JH "finite projective product ring equivalence counit"]
def counitIso : combine R S ⋙ factor R S ≅
    𝟭 (ModuleCat.FiniteProjective.{u, w} R × ModuleCat.FiniteProjective.{v, w} S) :=
  (equivalence R S).counitIso

/-- The finite-projective factorization functor is an equivalence. -/
@[stacks 00JH "finite projective product ring factor functor equivalence"]
instance factor_isEquivalence : (factor R S).IsEquivalence :=
  (equivalence R S).isEquivalence_functor

/-- The finite-projective combination functor is an equivalence. -/
@[stacks 00JH "finite projective product ring combination functor equivalence"]
instance combine_isEquivalence : (combine R S).IsEquivalence :=
  (equivalence R S).isEquivalence_inverse

end CategoryTheory.ModuleCat.Product.FiniteProjective
