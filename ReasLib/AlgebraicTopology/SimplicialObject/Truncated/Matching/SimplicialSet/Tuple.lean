module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.StructureMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Matching tuples of truncated simplicial sets

This file owns the explicit type of compatible face tuples for a truncated simplicial set,
together with its coordinate maps, functoriality, and degeneracies. It is independent of matching
limits and coskeletons.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u

namespace CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily

namespace Tuple

/-- Pointwise compatibility of a proposed tuple of faces in a truncated simplicial set. -/
@[stacks 0189 "compatible tuple of simplices"]
def Compatible {n : ℕ} (U : SSet.Truncated.{u} n)
    (face : Fin (n + 2) → U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) : Prop :=
  match n with
  | 0 => True
  | m + 1 =>
      ∀ i j : Fin (m + 2), i ≤ j →
        U.δ j (face i.castSucc) = U.δ i (face j.succ)

namespace Compatible

/-- In degree zero, every pair of vertices is a compatible matching tuple. -/
@[simp, stacks 0189 "zero-degree matching tuple compatibility"]
theorem zero (U : SSet.Truncated.{u} 0)
    (face : Fin 2 → U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    Tuple.Compatible U face := sorry

/-- In successor degree, tuple compatibility is exactly the pairwise face relation. -/
@[simp, stacks 0189 "successor matching tuple compatibility"]
theorem succ_iff {m : ℕ} (U : SSet.Truncated.{u} (m + 1))
    (face : Fin (m + 3) →
      U.obj (op (⦋m + 1⦌ₘ₊₁ : SimplexCategory.Truncated (m + 1)))) :
    Tuple.Compatible U face ↔
      ∀ i j : Fin (m + 2), i ≤ j →
        U.δ j (face i.castSucc) = U.δ i (face j.succ) := sorry

/-- The faces obtained from a simplicial degeneracy form a compatible matching tuple. -/
@[stacks 0189 "matching tuple degeneracy compatibility"]
theorem degeneracy {n : ℕ} (U : SSet.Truncated.{u} n)
    (j : Fin (n + 1))
    (x : U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    Tuple.Compatible U
      (fun i ↦ U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op x) := sorry

/-- Mapping every coordinate of a compatible tuple along a truncated simplicial morphism
preserves compatibility. -/
@[stacks 0189 "functoriality of matching-tuple compatibility"]
theorem map {n : ℕ} {U V : SSet.Truncated.{u} n}
    {face : Fin (n + 2) → U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))}
    (h : Tuple.Compatible U face) (α : U ⟶ V) :
    Tuple.Compatible V (fun i ↦
      α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) (face i)) := sorry

end Compatible

end Tuple

/-- The explicit type of compatible `(n + 2)`-tuples of `n`-simplices. -/
@[stacks 0189 "matching tuple of a truncated simplicial set"]
structure Tuple {n : ℕ} (U : SSet.Truncated.{u} n) where
  /-- The `i`-th face in the tuple. -/
  face (i : Fin (n + 2)) : U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))
  /-- The tuple satisfies the pairwise face compatibility equations. -/
  compatible : Tuple.Compatible U face

attribute [stacks 0189 "matching tuple face"] Tuple.face
attribute [stacks 0189 "matching tuple compatibility"] Tuple.compatible

namespace Tuple

variable {n : ℕ} {U : SSet.Truncated.{u} n}

/-- Two matching tuples are equal when all of their faces agree. -/
@[ext, stacks 0189 "matching tuple extensionality"]
theorem ext {x y : Tuple U} (h : ∀ i, x.face i = y.face i) : x = y := sorry

attribute [stacks 0189 "matching tuple extensionality criterion"] Tuple.ext_iff

/-- The `i`-th face projection from the explicit matching-tuple type. -/
@[stacks 0189 "matching tuple face projection"]
def π (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) :
    Tuple U ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) :=
  ↾fun x ↦ x.face i

/-- The face projection evaluates to the corresponding tuple coordinate. -/
@[simp, stacks 0189 "matching tuple face projection formula"]
theorem π.apply (i : Fin (n + 2)) (x : Tuple U) : π U i x = x.face i := sorry

/-- A truncated simplicial morphism maps a matching tuple coordinatewise. -/
@[stacks 0189 "map of matching tuples"]
def map {V : SSet.Truncated.{u} n} (α : U ⟶ V) : Tuple U ⟶ Tuple V :=
  ↾fun x ↦
    { face := fun i ↦
        α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) (x.face i)
      compatible := Compatible.map x.compatible α }

/-- Mapping a matching tuple is computed coordinatewise. -/
@[simp, stacks 0189 "matching-tuple map coordinate"]
theorem map_face {V : SSet.Truncated.{u} n} (α : U ⟶ V)
    (x : Tuple U) (i : Fin (n + 2)) :
    (map α x).face i =
      α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) (x.face i) := sorry

/-- Mapping matching tuples along an identity is the identity. -/
@[simp, stacks 0189 "identity map of matching tuples"]
theorem map_id (U : SSet.Truncated.{u} n) : map (𝟙 U) = 𝟙 (Tuple U) := sorry

/-- Maps of matching tuples preserve composition. -/
@[simp, stacks 0189 "composition of maps of matching tuples"]
theorem map_comp {V W : SSet.Truncated.{u} n} (α : U ⟶ V) (β : V ⟶ W) :
    map (α ≫ β) = map α ≫ map β := sorry

/-- A map of matching tuples commutes with each coordinate projection. -/
@[reassoc (attr := simp), stacks 0189 "map of matching tuples on projections"]
theorem map_π {V : SSet.Truncated.{u} n} (α : U ⟶ V) (i : Fin (n + 2)) :
    map α ≫ π V i =
      π U i ≫ α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) := sorry

/-- Explicit matching tuples form a functor of truncated simplicial sets. -/
@[stacks 0189 "matching-tuple functor"]
def functor (n : ℕ) : SSet.Truncated.{u} n ⥤ Type u where
  obj U := Tuple U
  map α := map α
  map_id U := Tuple.map_id U
  map_comp α β := Tuple.map_comp α β

/-- The matching-tuple functor evaluates to the explicit tuple type. -/
@[simp, stacks 0189 "matching-tuple functor object"]
theorem functor_obj {n : ℕ} (U : SSet.Truncated.{u} n) :
    (functor n).obj U = Tuple U := sorry

/-- The matching-tuple functor maps a morphism coordinatewise. -/
@[simp, stacks 0189 "matching-tuple functor map"]
theorem functor_map {V : SSet.Truncated.{u} n} (α : U ⟶ V) :
    (functor n).map α = map α := sorry

namespace functor

/-- The `i`-th tuple projection is natural in the truncated simplicial set. -/
@[stacks 0189 "natural matching-tuple projection"]
def π (i : Fin (n + 2)) :
    Tuple.functor n ⟶
      (evaluation ((SimplexCategory.Truncated n)ᵒᵖ) (Type u)).obj
        (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) where
  app U := Tuple.π U i
  naturality := fun {_ _} α ↦ Tuple.map_π α i

/-- The component of the natural tuple projection is the corresponding coordinate map. -/
@[simp, stacks 0189 "component of the natural matching-tuple projection"]
theorem π_app (i : Fin (n + 2)) (U : SSet.Truncated.{u} n) :
    (π i).app U = Tuple.π U i := sorry

end functor

/-- The `j`-th degeneracy into the matching-tuple type. -/
@[stacks 0189 "matching tuple degeneracy"]
def σ (U : SSet.Truncated.{u} n) (j : Fin (n + 1)) :
    U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ⟶ Tuple U :=
  ↾fun x ↦
    { face := fun i ↦ U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op x
      compatible := Compatible.degeneracy U j x }

/-- The `i`-th face of the `j`-th tuple degeneracy is induced by `δ_i ≫ σ_j`. -/
@[simp, stacks 0189 "matching tuple degeneracy face"]
theorem σ.face (U : SSet.Truncated.{u} n) (i : Fin (n + 2)) (j : Fin (n + 1))
    (x : U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    π U i (σ U j x) =
      U.map
        (SimplexCategory.Truncated.Hom.tr
          (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op x := sorry

/-- In degree zero, the unique tuple degeneracy sends `x` to `(x, x)`. -/
@[stacks 0189 "zero-degree matching tuple degeneracy"]
theorem σ.zero (U : SSet.Truncated.{u} 0)
    (x : U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (fun i : Fin 2 ↦ π U i (σ U 0 x)) = fun _ : Fin 2 ↦ x := sorry

/-- Mapping a tuple degeneracy along a truncated simplicial morphism agrees with first mapping
the simplex and then taking its tuple degeneracy. -/
@[reassoc (attr := simp), stacks 0189 "naturality of matching-tuple degeneracies"]
theorem map_σ {V : SSet.Truncated.{u} n} (α : U ⟶ V) (j : Fin (n + 1)) :
    α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ≫ σ V j =
      σ U j ≫ map α := sorry

namespace functor

/-- The `j`-th tuple degeneracy is natural in the truncated simplicial set. -/
@[stacks 0189 "natural matching-tuple degeneracy"]
def σ (j : Fin (n + 1)) :
    (evaluation ((SimplexCategory.Truncated n)ᵒᵖ) (Type u)).obj
        (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) ⟶
      Tuple.functor n where
  app U := Tuple.σ U j
  naturality := fun {_ _} α ↦ Tuple.map_σ α j

/-- The component of the natural tuple degeneracy is the explicit tuple degeneracy. -/
@[simp, stacks 0189 "component of the natural matching-tuple degeneracy"]
theorem σ_app (j : Fin (n + 1)) (U : SSet.Truncated.{u} n) :
    (σ j).app U = Tuple.σ U j := sorry

end functor

end Tuple

end CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily
