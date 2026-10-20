/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Functor

/-!
# Truncation of Eilenberg-MacLane simplicial objects

This file compares the canonical Dold-Kan model `K(B, k)` with the truncated simplicial object
concentrated in degree `k`, both objectwise and functorially in `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.truncation

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

/-- The component embedding a concentrated truncated object into the truncation of its explicit
Eilenberg-MacLane object. -/
@[stacks 0191 "Eilenberg-MacLane truncation comparison component"]
noncomputable def homApp (B : A) (k : ℕ)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (Truncated.concentrated B k).obj X ⟶
      ((SimplicialObject.truncation k).obj (eilenbergMacLane B k)).obj X :=
  if hX : X.unop.1.len = k then
    eqToHom (if_pos hX) ≫
      (singleObjXIsoOfEq (ComplexShape.down ℕ) k B X.unop.1.len hX).inv ≫
      ((AlgebraicTopology.DoldKan.Γ₀.splitting
        ((single A (ComplexShape.down ℕ) k).obj B)).cofan
          (Opposite.op X.unop.1)).inj
        (SimplicialObject.Splitting.IndexSet.id (Opposite.op X.unop.1))
  else 0

/-- The component projecting the truncation of an Eilenberg-MacLane object onto its unique
top-degree identity summand. -/
@[stacks 0191 "Eilenberg-MacLane truncation comparison inverse component"]
noncomputable def invApp (B : A) (k : ℕ)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    ((SimplicialObject.truncation k).obj (eilenbergMacLane B k)).obj X ⟶
      (Truncated.concentrated B k).obj X :=
  if hX : X.unop.1.len = k then
    (AlgebraicTopology.DoldKan.Γ₀.splitting
      ((single A (ComplexShape.down ℕ) k).obj B)).πSummand
        (SimplicialObject.Splitting.IndexSet.id (Opposite.op X.unop.1)) ≫
      (singleObjXIsoOfEq (ComplexShape.down ℕ) k B X.unop.1.len hX).hom ≫
        eqToHom (if_pos hX).symm
  else 0

/-- The truncation comparison components are natural in truncated simplex operators. -/
@[stacks 0191 "Eilenberg-MacLane truncation comparison naturality"]
theorem homApp.naturality (B : A) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    (Truncated.concentrated B k).map f ≫ homApp B k Y =
      homApp B k X ≫
        ((SimplicialObject.truncation k).obj (eilenbergMacLane B k)).map f := sorry

/-- The inverse truncation comparison components are natural in truncated simplex operators. -/
@[stacks 0191 "Eilenberg-MacLane truncation inverse naturality"]
theorem invApp.naturality (B : A) (k : ℕ)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (f : X ⟶ Y) :
    ((SimplicialObject.truncation k).obj (eilenbergMacLane B k)).map f ≫ invApp B k Y =
      invApp B k X ≫ (Truncated.concentrated B k).map f := sorry

/-- The natural transformation from the concentrated object to the truncated
Eilenberg-MacLane object. -/
@[stacks 0191 "Eilenberg-MacLane truncation comparison"]
noncomputable def hom (B : A) (k : ℕ) :
    Truncated.concentrated B k ⟶
      (SimplicialObject.truncation k).obj (eilenbergMacLane B k) where
  app := homApp B k
  naturality _ _ f := homApp.naturality B k f

/-- The natural transformation projecting a truncated Eilenberg-MacLane object onto the
concentrated object. -/
@[stacks 0191 "Eilenberg-MacLane truncation inverse"]
noncomputable def inv (B : A) (k : ℕ) :
    (SimplicialObject.truncation k).obj (eilenbergMacLane B k) ⟶
      Truncated.concentrated B k where
  app := invApp B k
  naturality _ _ f := invApp.naturality B k f

/-- The component of the truncation comparison is `homApp`. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation comparison component formula"]
theorem hom_app (B : A) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (hom B k).app X = homApp B k X := sorry

/-- The component of the inverse truncation comparison is `invApp`. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation inverse component formula"]
theorem inv_app (B : A) (k : ℕ) (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (inv B k).app X = invApp B k X := sorry

/-- The truncation comparison followed by its projection is the identity. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation forward inverse law"]
theorem hom_comp_inv (B : A) (k : ℕ) : hom B k ≫ inv B k = 𝟙 _ := sorry

/-- The projection followed by the truncation comparison is the identity. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation inverse forward law"]
theorem inv_comp_hom (B : A) (k : ℕ) : inv B k ≫ hom B k = 𝟙 _ := sorry

/-- The explicit objectwise comparison between a concentrated truncated object and the
truncation of its Eilenberg-MacLane object. -/
@[stacks 0191 "truncation of an Eilenberg-MacLane object"]
noncomputable def objIso (B : A) (k : ℕ) :
    Truncated.concentrated B k ≅
      (SimplicialObject.truncation k).obj (eilenbergMacLane B k) where
  hom := hom B k
  inv := inv B k
  hom_inv_id := hom_comp_inv B k
  inv_hom_id := inv_comp_hom B k

/-- The forward map of `objIso` is the explicit truncation comparison. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation isomorphism forward map"]
theorem objIso.hom (B : A) (k : ℕ) : (objIso B k).hom = hom B k := sorry

/-- The inverse map of `objIso` is the explicit truncation projection. -/
@[simp, stacks 0191 "Eilenberg-MacLane truncation isomorphism inverse map"]
theorem objIso.inv (B : A) (k : ℕ) : (objIso B k).inv = inv B k := sorry

/-- The objectwise truncation comparisons are natural in the coefficient object. -/
@[stacks 0191 "naturality of the Eilenberg-MacLane truncation isomorphism"]
theorem objIso.hom_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    Truncated.concentrated.map k f ≫ (objIso D k).hom =
      (objIso B k).hom ≫
        (eilenbergMacLane.functor k ⋙ SimplicialObject.truncation k).map f := sorry

/-- The inverse objectwise truncation comparisons are natural in the coefficient object. -/
@[stacks 0191 "inverse naturality of the Eilenberg-MacLane truncation isomorphism"]
theorem objIso.inv_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    (eilenbergMacLane.functor k ⋙ SimplicialObject.truncation k).map f ≫
        (objIso D k).inv =
      (objIso B k).inv ≫ Truncated.concentrated.map k f := sorry

/-- Concentrated truncated objects are naturally isomorphic to truncations of the
Eilenberg-MacLane functor. -/
@[stacks 0191 "functorial Eilenberg-MacLane truncation comparison"]
noncomputable def iso (k : ℕ) :
    Truncated.concentrated.functor (A := A) k ≅
      eilenbergMacLane.functor k ⋙ SimplicialObject.truncation k :=
  NatIso.ofComponents (fun B ↦ objIso B k) (fun f ↦ objIso.hom_naturality k f)

/-- The component of the functorial truncation comparison is the explicit objectwise
isomorphism. -/
@[simp, stacks 0191 "functorial Eilenberg-MacLane truncation component formula"]
theorem iso_app (k : ℕ) (B : A) :
    (iso (A := A) k).app B = objIso B k := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.truncation

namespace CategoryTheory.SimplicialObject.eilenbergMacLane

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasFiniteCoproducts A]

/-- The ambient degree-`k` term of the canonical Eilenberg--MacLane object is canonically `B`.
This coefficient-level comparison is separated from normalized-complex conventions so it can be
reused by both the `d₀` and source-signed lower-face APIs. -/
@[stacks 0191 "Eilenberg-MacLane top degree comparison"]
noncomputable def degreeIso (B : A) (k : ℕ) :
    (eilenbergMacLane B k).obj
        (Opposite.op ⦋k⦌) ≅ B where
  hom :=
    (truncation.objIso B k).inv.app
        (Opposite.op (Truncated.concentrated.top k)) ≫
      (Truncated.concentrated.topIso B k).inv
  inv :=
    (Truncated.concentrated.topIso B k).hom ≫
      (truncation.objIso B k).hom.app
        (Opposite.op (Truncated.concentrated.top k))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The ambient top-degree comparison is natural in the coefficient object. -/
@[stacks 0191 "naturality of Eilenberg-MacLane top degree comparison"]
theorem degreeIso.hom_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    ((eilenbergMacLane.functor k).map f).app (Opposite.op ⦋k⦌) ≫ (degreeIso D k).hom =
      (degreeIso B k).hom ≫ f := sorry

/-- The inverse ambient top-degree comparison is natural in the coefficient object. -/
@[stacks 0191 "inverse naturality of Eilenberg-MacLane top degree comparison"]
theorem degreeIso.inv_naturality (k : ℕ) {B D : A} (f : B ⟶ D) :
    f ≫ (degreeIso D k).inv =
      (degreeIso B k).inv ≫
        ((eilenbergMacLane.functor k).map f).app (Opposite.op ⦋k⦌) := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane
