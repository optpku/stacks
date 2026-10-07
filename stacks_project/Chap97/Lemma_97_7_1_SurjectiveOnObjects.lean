module

public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable

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

/-- Unfolding of `existsFieldValuedLift` as a field extension over `S` together
with a 2-isomorphic lift of `y` after restriction. -/
theorem existsFieldValuedLift_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y) :
    existsFieldValuedLift f y ↔
      ∃ (K : Type u) (_ : Field K) (τ : Spec (.of K) ⟶ S)
        (e : Spec (.of K) ⟶ Spec (.of k)) (he : e ≫ σ = τ)
        (x : GroupoidsOver.slice (Over.mk τ) ⟶ X),
        Nonempty
          (x ≫ f ≅
            FiberedCategoryOver.Groupoids.slice.pullback (Over.homMk e he : Over.mk τ ⟶ Over.mk σ) y) :=
  sorry

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

/-- A 1-morphism that is surjective on objects admits a field-valued lift of
every object of the target over a field. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [SurjectiveOnObjects f] {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y) :
    existsFieldValuedLift f y := sorry

/-- A 1-morphism is surjective on objects as soon as every field-valued object
of the target lifts after a field extension. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (h_exists_lift :
      ∀ {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)
        (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y), existsFieldValuedLift f y) :
    SurjectiveOnObjects f := sorry

/-- If `f : X ⟶ Y` is surjective on objects, then so is its base change
`TwoFibreProduct.fst g f : X ×_Y Z ⟶ Z` along any `g : Z ⟶ Y`. -/
theorem pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [SurjectiveOnObjects f] :
    SurjectiveOnObjects (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) :=
  sorry

end SurjectiveOnObjects

end AlgebraicGeometry.Groupoids.Hom
