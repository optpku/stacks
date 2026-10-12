/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Object

/-!
# Functorial concentrated truncated simplicial objects

This leaf packages `Truncated.concentrated B k` functorially in `B` and exposes the canonical
isomorphism between `B` and its top-degree value.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

namespace concentrated

variable [HasZeroObject A]

/-- The component of the morphism between concentrated truncated simplicial objects induced by a
morphism of their top-degree values. -/
@[stacks 018Y "concentrated object morphism component"]
noncomputable def mapApp (k : ℕ) {B D : A} (f : B ⟶ D)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (concentrated B k).obj X ⟶ (concentrated D k).obj X :=
  if hX : X.unop.1.len = k then
    eqToHom (if_pos hX) ≫ f ≫ eqToHom (if_pos hX).symm
  else 0

/-- The components induced by a morphism of top-degree values commute with every truncated
simplex operator. -/
@[stacks 018Y "concentrated object morphism component naturality"]
theorem mapApp.naturality (k : ℕ) {B D : A} (f : B ⟶ D)
    {X Y : (SimplexCategory.Truncated k)ᵒᵖ} (φ : X ⟶ Y) :
    (concentrated B k).map φ ≫ mapApp k f Y =
      mapApp k f X ≫ (concentrated D k).map φ := sorry

/-- A morphism of top-degree values induces a morphism of concentrated truncated simplicial
objects. -/
@[stacks 018Y "concentrated object functorial morphism"]
noncomputable def map (k : ℕ) {B D : A} (f : B ⟶ D) :
    concentrated B k ⟶ concentrated D k where
  app X := mapApp k f X
  naturality _ _ φ := mapApp.naturality k f φ

/-- A concentrated morphism is computed degreewise by `mapApp`. -/
@[simp, stacks 018Y "concentrated object morphism component formula"]
theorem map_app (k : ℕ) {B D : A} (f : B ⟶ D)
    (X : (SimplexCategory.Truncated k)ᵒᵖ) :
    (map k f).app X = mapApp k f X := sorry

/-- The concentrated morphism induced by an identity is the identity. -/
@[stacks 018Y "concentrated functorial morphism identity law"]
theorem map.id (B : A) (k : ℕ) :
    map k (𝟙 B) = 𝟙 (concentrated B k) := sorry

/-- Concentrated morphisms preserve composition of their top-degree maps. -/
@[stacks 018Y "concentrated functorial morphism composition law"]
theorem map.comp (k : ℕ) {B D E : A} (f : B ⟶ D) (g : D ⟶ E) :
    map k (f ≫ g) = map k f ≫ map k g := sorry

/-- Concentrated `k`-truncated simplicial objects depend functorially on their unique nonzero
value. -/
@[stacks 018Y "concentrated truncated simplicial object functor"]
noncomputable def functor (k : ℕ) : A ⥤ SimplicialObject.Truncated A k where
  obj B := concentrated B k
  map f := map k f
  map_id B := concentrated.map.id B k
  map_comp f g := concentrated.map.comp k f g

/-- The concentrated-object functor sends `B` to `concentrated B k`. -/
@[simp, stacks 018Y "concentrated functor object formula"]
theorem functor_obj (k : ℕ) (B : A) :
    (functor (A := A) k).obj B = concentrated B k := sorry

/-- The concentrated-object functor sends `f` to the corresponding degreewise morphism. -/
@[simp, stacks 018Y "concentrated functor map formula"]
theorem functor_map (k : ℕ) {B D : A} (f : B ⟶ D) :
    (functor (A := A) k).map f = map k f := sorry

/-- The forward map from `B` to the top value of `concentrated B k`. -/
/- no direct Stacks tag: explicit comparison helpers for the concentrated setup. -/
def topHom (B : A) (k : ℕ) : B ⟶ (concentrated B k).obj (op (top k)) :=
  eqToHom (if_pos rfl).symm

/-- The inverse map from the top value of `concentrated B k` to `B`. -/
def topInv (B : A) (k : ℕ) : (concentrated B k).obj (op (top k)) ⟶ B :=
  eqToHom (if_pos rfl)

/-- The two explicit top comparison maps compose to the identity of `B`. -/
theorem topHom_comp_topInv (B : A) (k : ℕ) :
    topHom B k ≫ topInv B k = 𝟙 B := sorry

/-- The two explicit top comparison maps compose to the identity of the concentrated top value. -/
theorem topInv_comp_topHom (B : A) (k : ℕ) :
    topInv B k ≫ topHom B k =
      𝟙 ((concentrated B k).obj (op (top k))) := sorry

/-- The explicit isomorphism from `B` to the top value of `concentrated B k`. -/
def topIso (B : A) (k : ℕ) : B ≅ (concentrated B k).obj (op (top k)) where
  hom := topHom B k
  inv := topInv B k
  hom_inv_id := topHom_comp_topInv B k
  inv_hom_id := topInv_comp_topHom B k

/-- The forward map of the concentrated top isomorphism is `topHom`. -/
@[simp]
theorem topIso_hom (B : A) (k : ℕ) :
    (topIso B k).hom = topHom B k := sorry

/-- The inverse map of the concentrated top isomorphism is `topInv`. -/
@[simp]
theorem topIso_inv (B : A) (k : ℕ) :
    (topIso B k).inv = topInv B k := sorry

end concentrated

end CategoryTheory.SimplicialObject.Truncated
