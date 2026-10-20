/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Coproducts of schemes over a base

The structure morphisms of a small family of schemes over a fixed base induce a structure
morphism on their coproduct, and each summand inclusion is a morphism over the base.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Coproduct

variable {S : Scheme.{u}}

/-- The object of `Over S` whose underlying scheme is the coproduct of a small family of
schemes over `S`. -/
def overMk {I : Type v} [small : Small.{u} I] (U : I → Over S) : Over S :=
  Over.mk (Sigma.desc fun i ↦ (U i).hom)

/-- The underlying scheme of `overMk U` is the coproduct of the underlying schemes. -/
theorem overMk_left {I : Type v} [small : Small.{u} I] (U : I → Over S) :
    (overMk U).left = ∐ fun i ↦ (U i).left :=
  rfl

/-- The structure morphism of `overMk U` is the coproduct descent of the structure morphisms. -/
theorem overMk_hom {I : Type v} [small : Small.{u} I] (U : I → Over S) :
    (overMk U).hom = Sigma.desc fun i ↦ (U i).hom :=
  rfl

/-- The coproduct inclusion of a summand commutes with the structure morphisms to `S`. -/
theorem overι_w {I : Type v} [small : Small.{u} I] (U : I → Over S) (i : I) :
    Sigma.ι (fun j ↦ (U j).left) i ≫ (overMk U).hom = (U i).hom :=
  Sigma.ι_desc (fun j ↦ (U j).hom) i

/-- The inclusion of the `i`-th summand into the scheme coproduct, as a morphism over `S`. -/
def overι {I : Type v} [small : Small.{u} I] (U : I → Over S) (i : I) : U i ⟶ overMk U :=
  Over.homMk (Sigma.ι (fun j ↦ (U j).left) i) (overι_w U i)

/-- The underlying scheme morphism of `overι U i` is the coproduct inclusion. -/
theorem overι_left {I : Type v} [small : Small.{u} I] (U : I → Over S) (i : I) :
    (overι U i).left = Sigma.ι (fun j ↦ (U j).left) i :=
  rfl

end AlgebraicGeometry.Scheme.Coproduct
