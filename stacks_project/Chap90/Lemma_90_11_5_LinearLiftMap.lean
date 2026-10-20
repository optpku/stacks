/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.LinearLift.NatTrans

/-!
# Morphisms of linear lifts

A natural transformation of finite-product-preserving functors to types,
each sending the zero object to a singleton, induces a morphism of the
associated `R`-linear lifts, with the same underlying components.
-/

@[expose] public section

open CategoryTheory hiding Linear
open Limits ZeroObject

noncomputable section

universe u v w

namespace CategoryTheory.Functor

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasBinaryProducts C]
variable {R : Type u} [CommRing R]
variable [CategoryTheory.Linear R C] [HasFiniteProducts C] [HasZeroObject C]
variable {L₁ L₂ : C ⥤ Type v}
variable [PreservesFiniteProducts L₁] [Unique (L₁.obj 0)]
variable [PreservesFiniteProducts L₂] [Unique (L₂.obj 0)]

#check (CategoryTheory.Functor.linearLiftApp :
  ∀ (t : L₁ ⟶ L₂) (M : C), L₁.obj M →ₗ[R] L₂.obj M)

#check (CategoryTheory.Functor.linearLiftNatTrans :
  ∀ (t : L₁ ⟶ L₂),
    (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ (linearLift L₂ : C ⥤ ModuleCat.{v} R))

#check (CategoryTheory.Functor.linearLiftApp_apply :
  ∀ (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M),
    (linearLiftApp t M : L₁.obj M →ₗ[R] L₂.obj M) x = t.app M x)

#check (CategoryTheory.Functor.linearLiftNatTrans_app :
  ∀ (t : L₁ ⟶ L₂) (M : C),
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M =
      ModuleCat.ofHom (linearLiftApp t M))

#check (CategoryTheory.Functor.linearLiftNatTrans_apply :
  ∀ (t : L₁ ⟶ L₂) (M : C) (x : L₁.obj M),
    (linearLiftNatTrans t : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂).app M x =
      t.app M x)

#check (CategoryTheory.Functor.forget_map_linearLiftNatTrans_app :
  ∀ (t : L₁ ⟶ L₂) (M : C),
    (forget (ModuleCat.{v} R)).map ((linearLiftNatTrans t).app M) = t.app M)

#check (CategoryTheory.Functor.linearLiftNatTrans_unique :
  ∀ (t : L₁ ⟶ L₂)
    (α : (linearLift L₁ : C ⥤ ModuleCat.{v} R) ⟶ linearLift L₂),
    (∀ M, (forget (ModuleCat.{v} R)).map (α.app M) = t.app M) →
      α = linearLiftNatTrans t)

end CategoryTheory.Functor
