module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.StructureMaps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit face families for truncated simplicial objects

This file gives the coordinate presentation of compatible face families. It is kept independent
of both the presheaf packaging and the structured-arrow matching diagram, so later comparison
layers do not make either presentation the implementation of the other.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.matching

variable {C : Type u} [Category.{v} C]

namespace FaceFamily

/-- Compatibility of the face coordinates of a prospective simplex. In positive degree, for
`i ≤ j`, the `i`-th coordinate followed by the `j`-th face equals the `(j + 1)`-st coordinate
followed by the `i`-th face. In degree zero there are no compatibility equations. -/
@[stacks 0186 "explicit matching face compatibility"]
def Compatible {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (app : ∀ _ : Fin (n + 2),
      T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) : Prop :=
  match n with
  | 0 => True
  | m + 1 =>
      ∀ i j : Fin (m + 2), i ≤ j →
        app i.castSucc ≫ U.δ j = app j.succ ≫ U.δ i

end FaceFamily

/-- An explicit matching face family for the next degree of a truncated simplicial object.
Its coordinates are maps to the current top degree, subject precisely to the simplicial face
compatibility relations. -/
@[stacks 0186 "explicit matching face family"]
structure FaceFamily {n : ℕ} (U : SimplicialObject.Truncated C n) (T : C) where
  /-- The face coordinate indexed by `i : Fin (n + 2)`. -/
  app (i : Fin (n + 2)) :
    T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))
  /-- The face coordinates satisfy the matching compatibility equations. -/
  compatible : FaceFamily.Compatible U app

attribute [stacks 0186 "explicit matching face coordinate"] FaceFamily.app
attribute [stacks 0186 "explicit matching face compatibility law"] FaceFamily.compatible

namespace FaceFamily

variable {n : ℕ} {U V W : SimplicialObject.Truncated C n} {S T R : C}

/-- In degree zero the matching compatibility predicate has no equations. -/
@[simp, stacks 0186 "zero-degree face compatibility"]
theorem Compatible.zero (U : SimplicialObject.Truncated C 0) {T : C}
    (app : ∀ i : Fin 2,
      T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    Compatible U app := sorry

/-- In successor degree, matching compatibility is exactly the family of pairwise face
relations indexed in the same form as `SimplicialObject.δ_comp_δ`. -/
@[simp, stacks 0186 "successor face compatibility"]
theorem Compatible.succ_iff {m : ℕ} (U : SimplicialObject.Truncated C (m + 1)) {T : C}
    (app : ∀ i : Fin (m + 3),
      T ⟶ U.obj (op (⦋m + 1⦌ₘ₊₁ : SimplexCategory.Truncated (m + 1)))) :
    Compatible U app ↔
      ∀ i j : Fin (m + 2), i ≤ j →
        app i.castSucc ≫ U.δ j = app j.succ ≫ U.δ i := sorry

namespace Compatible

/-- Precomposition of every coordinate preserves matching-face compatibility. -/
@[stacks 0186 "face compatibility under precomposition"]
theorem precomp
    {app : ∀ i : Fin (n + 2),
      T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))}
    (h : FaceFamily.Compatible U app) (f : S ⟶ T) :
    FaceFamily.Compatible U (fun i ↦ f ≫ app i) := sorry

/-- Postcomposition along a morphism of truncated simplicial objects preserves matching-face
compatibility. -/
@[stacks 0186 "face compatibility under a truncated simplicial map"]
theorem map
    {app : ∀ i : Fin (n + 2),
      T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))}
    (h : FaceFamily.Compatible U app) (α : U ⟶ V) :
    FaceFamily.Compatible V
      (fun i ↦ app i ≫ α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) := sorry

end Compatible

/-- Two explicit face families are equal when all their coordinates are equal. -/
@[ext, stacks 0186 "explicit matching face-family extensionality"]
theorem ext {F G : FaceFamily U T} (h : ∀ i, F.app i = G.app i) : F = G := sorry

/-- The degree-zero face family determined by its two unrestricted coordinates. -/
@[stacks 0186 "zero-degree explicit matching face family"]
def zero (U : SimplicialObject.Truncated C 0) {T : C}
    (f₀ f₁ : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    FaceFamily U T where
  app := Fin.cases f₀ (fun _ ↦ f₁)
  compatible := Compatible.zero U _

/-- The zeroth coordinate of a degree-zero face family is its first supplied map. -/
@[simp, stacks 0186 "zero-degree face-family first coordinate"]
theorem zero.app_zero (U : SimplicialObject.Truncated C 0) {T : C}
    (f₀ f₁ : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (zero U f₀ f₁).app 0 = f₀ := sorry

/-- The first coordinate of a degree-zero face family is its second supplied map. -/
@[simp, stacks 0186 "zero-degree face-family second coordinate"]
theorem zero.app_one (U : SimplicialObject.Truncated C 0) {T : C}
    (f₀ f₁ : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (zero U f₀ f₁).app 1 = f₁ := sorry

/-- Every degree-zero face family is recovered from its two coordinates. -/
@[simp, stacks 0186 "zero-degree face-family reconstruction"]
theorem zero.eta {U : SimplicialObject.Truncated C 0} {T : C} (F : FaceFamily U T) :
    zero U (F.app 0) (F.app 1) = F := sorry

/-- A successor-degree face family constructed from coordinates satisfying the explicit pairwise
compatibility equations. -/
@[stacks 0186 "successor explicit matching face family"]
def succ {m : ℕ} (U : SimplicialObject.Truncated C (m + 1)) {T : C}
    (app : ∀ _ : Fin (m + 3),
      T ⟶ U.obj (op (⦋m + 1⦌ₘ₊₁ : SimplexCategory.Truncated (m + 1))))
    (compatible : ∀ i j : Fin (m + 2), i ≤ j →
      app i.castSucc ≫ U.δ j = app j.succ ≫ U.δ i) :
    FaceFamily U T where
  app := app
  compatible := compatible

/-- A successor face family evaluates to its supplied coordinate family. -/
@[simp, stacks 0186 "successor face-family coordinate"]
theorem succ.app {m : ℕ} (U : SimplicialObject.Truncated C (m + 1)) {T : C}
    (app : ∀ i : Fin (m + 3),
      T ⟶ U.obj (op (⦋m + 1⦌ₘ₊₁ : SimplexCategory.Truncated (m + 1))))
    (compatible : ∀ i j : Fin (m + 2), i ≤ j →
      app i.castSucc ≫ U.δ j = app j.succ ≫ U.δ i)
    (i : Fin (m + 3)) :
    (succ U app compatible).app i = app i := sorry

/-- Precomposition makes a matching face family contravariant in its test object. -/
@[stacks 0186 "explicit matching face-family precomposition"]
def precomp (F : FaceFamily U T) (f : S ⟶ T) : FaceFamily U S where
  app i := f ≫ F.app i
  compatible := F.compatible.precomp f

/-- Precomposition is computed coordinatewise. -/
@[simp, reassoc, stacks 0186 "face-family precomposition formula"]
theorem precomp.app (F : FaceFamily U T) (f : S ⟶ T) (i : Fin (n + 2)) :
    (F.precomp f).app i = f ≫ F.app i := sorry

/-- Precomposition by an identity leaves a face family unchanged. -/
@[simp, stacks 0186 "face-family precomposition identity"]
theorem precomp.id (F : FaceFamily U T) : F.precomp (𝟙 T) = F := sorry

/-- Iterated precomposition agrees with precomposition by the composite. -/
@[simp, stacks 0186 "face-family precomposition composition"]
theorem precomp.comp (F : FaceFamily U T) (f : S ⟶ T) (g : R ⟶ S) :
    (F.precomp f).precomp g = F.precomp (g ≫ f) := sorry

/-- Postcomposition with a morphism of truncated simplicial objects maps matching face families
coordinatewise. -/
@[stacks 0186 "explicit matching face-family map"]
def map (F : FaceFamily U T) (α : U ⟶ V) : FaceFamily V T where
  app i := F.app i ≫ α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n))
  compatible := F.compatible.map α

/-- Mapping a face family along a morphism of truncated simplicial objects is computed
coordinatewise. -/
@[simp, reassoc, stacks 0186 "face-family map formula"]
theorem map.app (F : FaceFamily U T) (α : U ⟶ V) (i : Fin (n + 2)) :
    (F.map α).app i =
      F.app i ≫ α.app (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) := sorry

/-- Mapping a face family along an identity leaves it unchanged. -/
@[simp, stacks 0186 "face-family map identity"]
theorem map.id (F : FaceFamily U T) : F.map (𝟙 U) = F := sorry

/-- Successive maps of face families agree with the composite map. -/
@[simp, stacks 0186 "face-family map composition"]
theorem map.comp (F : FaceFamily U T) (α : U ⟶ V) (β : V ⟶ W) :
    (F.map α).map β = F.map (α ≫ β) := sorry

/-- Precomposition in the test object commutes with mapping the truncated simplicial object. -/
@[simp, stacks 0186 "face-family map-precomposition interchange"]
theorem map.precomp (F : FaceFamily U T) (f : S ⟶ T) (α : U ⟶ V) :
    (F.precomp f).map α = (F.map α).precomp f := sorry

end FaceFamily
end CategoryTheory.SimplicialObject.Truncated.matching
