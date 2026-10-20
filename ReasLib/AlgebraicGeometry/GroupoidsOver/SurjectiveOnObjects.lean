/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# 1-morphisms of groupoid fibrations that are surjective on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is surjective
on objects when every object of the target over the spectrum of a field lifts
after a field extension over `S`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.Groupoids.Hom

/-- Existence of a field extension `K / k` over `S` and an object `x` of `X`
over `Spec(K)` such that `x ≫ f` is 2-isomorphic to the restriction of `y`
along `Spec(K) ⟶ Spec(k)`. -/
def existsFieldValuedLift {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y) : Prop :=
  ∃ (K : Type u) (_ : Field K) (τ : Spec (.of K) ⟶ S)
    (e : Spec (.of K) ⟶ Spec (.of k)) (he : e ≫ σ = τ)
    (x : GroupoidsOver.slice (Over.mk τ) ⟶ X),
    Nonempty
      (x ≫ f ≅
        FiberedCategoryOver.Groupoids.slice.pullback (Over.homMk e he : Over.mk τ ⟶ Over.mk σ) y)

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf` is surjective on objects when, for every field `k` over `S` and
every object `y` of `Y` over `Spec(k)`, there exist a field extension `K / k`
over `S` and an object `x` of `X` over `Spec(K)` with `x ≫ f` 2-isomorphic to
`y` restricted to `Spec(K)`. -/
class SurjectiveOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop where
  /-- Every field-valued object of `Y` lifts after a field extension over `S`. -/
  exists_lift :
    ∀ {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)
      (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y), existsFieldValuedLift f y

namespace SurjectiveOnObjects

/-- The identity 1-morphism of a category fibred in groupoids is surjective on
objects. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    SurjectiveOnObjects (𝟙 X) := sorry

/-- If `f : X ⟶ Y` is surjective on objects, then so is its base change
`TwoFibreProduct.fst g f : X ×_Y Z ⟶ Z` along any `g : Z ⟶ Y`. -/
instance pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [SurjectiveOnObjects f] :
    SurjectiveOnObjects (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) :=
  sorry

/-- The composition of two 1-morphisms of categories fibred in groupoids that
are surjective on objects is surjective on objects. -/
instance comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnObjects f] [SurjectiveOnObjects g] :
    SurjectiveOnObjects (f ≫ g) := sorry

end SurjectiveOnObjects

end AlgebraicGeometry.Groupoids.Hom
