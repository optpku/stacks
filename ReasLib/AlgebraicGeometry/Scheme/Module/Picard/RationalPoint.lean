/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.FlatDescent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Restriction of invertible modules along rational points

This file provides the geometric restriction maps induced by rational points of open
subschemes of affine space and compares the resulting restrictions of invertible modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenAffineSpace

variable {k : Type u} [Field k] {n : ℕ}

/-- The structure morphism from an open subscheme of affine space over `Spec(k)` to its base. -/
abbrev toBase
    (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens) :
    U.toScheme ⟶ Spec (CommRingCat.of k) :=
  U.ι ≫ (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))

/-- The fiber product of a scheme over `Spec(k)` with an open subscheme of affine space. -/
def product
    (X : Over (Spec (CommRingCat.of k)))
    (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens) : Scheme :=
  pullback X.hom (toBase U)

/-- The morphism from a scheme to its product with an open affine-space subscheme induced by a
chosen rational point. -/
def restrictionMap
    (X : Over (Spec (CommRingCat.of k)))
    (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens)
    (p : Spec (CommRingCat.of k) ⟶ U.toScheme)
    (hp : p ≫ toBase U = 𝟙 (Spec (CommRingCat.of k))) :
    X.left ⟶ product X U :=
  pullback.lift (𝟙 X.left) (X.hom ≫ p) (by
    simp only [Category.id_comp, Category.assoc, hp, Category.comp_id])

/-- The pullback of a module along the product section induced by a chosen rational point. -/
def restrictionModule
    (X : Over (Spec (CommRingCat.of k)))
    (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens)
    (p : Spec (CommRingCat.of k) ⟶ U.toScheme)
    (hp : p ≫ toBase U = 𝟙 (Spec (CommRingCat.of k)))
    (ℒ : (product X U).Modules) : X.left.Modules :=
  (Scheme.Modules.pullback (restrictionMap X U p hp)).obj ℒ

/-- For a normal variety, the restrictions of an invertible module on its product with an open
subscheme of affine space along any two rational points are isomorphic. -/
@[stacks 0BEH]
theorem restrictionModule_iso_of_normalVariety
    (X : Over (Spec (CommRingCat.of k))) [Variety X] (hXnormal : X.left.isNormal)
    (U : (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of k))).Opens)
    (p q : Spec (CommRingCat.of k) ⟶ U.toScheme)
    (hp : p ≫ toBase U = 𝟙 (Spec (CommRingCat.of k)))
    (hq : q ≫ toBase U = 𝟙 (Spec (CommRingCat.of k)))
    (ℒ : (product X U).Modules) [Scheme.Modules.Invertible ℒ] :
    Nonempty (restrictionModule X U p hp ℒ ≅ restrictionModule X U q hq ℒ) := sorry

end AlgebraicGeometry.Scheme.OpenAffineSpace
