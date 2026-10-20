/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily.Presheaf
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.SimplicialSet.Tuple
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Representability by matching tuples

Compatible face families of a truncated simplicial set are represented by its explicit matching
tuple type. The representation is natural in the truncated simplicial set.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u

namespace CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple

variable {n : ℕ} {U : SSet.Truncated.{u} n}

namespace Compatible

/-- A family of compatible tuples determines a compatible categorical face family. -/
@[stacks 0189 "matching tuples to face-family compatibility"]
theorem faceFamily {T : Type u} (f : T ⟶ Tuple U) :
    FaceFamily.Compatible U (fun i ↦ ↾fun t ↦ (f t).face i) := sorry

/-- Evaluating a categorical face family at a point gives a compatible tuple. -/
@[stacks 0189 "face family to matching-tuple compatibility"]
theorem ofFaceFamily {T : Type u} (F : FaceFamily U T) (t : T) :
    Tuple.Compatible U (fun i ↦ F.app i t) := sorry

end Compatible

/-- Convert a map to matching tuples into its compatible family of face coordinates. -/
@[stacks 0189 "map to matching tuples as a face family"]
def toFaceFamily {T : Type u} (f : T ⟶ Tuple U) : FaceFamily U T where
  app i := ↾fun t ↦ (f t).face i
  compatible := Compatible.faceFamily f

/-- Converting a map to matching tuples is computed coordinatewise. -/
@[simp, stacks 0189 "map-to-face-family coordinate"]
theorem toFaceFamily.app {T : Type u} (f : T ⟶ Tuple U)
    (i : Fin (n + 2)) (t : T) :
    (toFaceFamily f).app i t = (f t).face i := sorry

/-- Reconstruct a map to matching tuples from a compatible face family. -/
@[stacks 0189 "face family to a map of matching tuples"]
def ofFaceFamily {T : Type u} (F : FaceFamily U T) : T ⟶ Tuple U :=
  ↾fun t ↦
    { face := fun i ↦ F.app i t
      compatible := Compatible.ofFaceFamily F t }

/-- Reconstructing a map from a face family recovers every coordinate. -/
@[simp, stacks 0189 "face-family-to-map coordinate"]
theorem ofFaceFamily.face {T : Type u} (F : FaceFamily U T)
    (i : Fin (n + 2)) (t : T) :
    (ofFaceFamily F t).face i = F.app i t := sorry

/-- Reconstructing after extracting coordinates is the identity on maps to matching tuples. -/
@[stacks 0189 "matching tuple equivalence left inverse"]
theorem homEquiv.left_inv {T : Type u} (f : T ⟶ Tuple U) :
    ofFaceFamily (toFaceFamily f) = f := sorry

/-- Extracting coordinates after reconstruction is the identity on compatible face families. -/
@[stacks 0189 "matching tuple equivalence right inverse"]
theorem homEquiv.right_inv {T : Type u} (F : FaceFamily U T) :
    toFaceFamily (ofFaceFamily F) = F := sorry

/-- Maps into the matching-tuple type are equivalent to explicit compatible face families. -/
@[stacks 0189 "maps to matching tuples as face families"]
def homEquiv (U : SSet.Truncated.{u} n) (T : Type u) :
    (T ⟶ Tuple U) ≃ FaceFamily U T where
  toFun := toFaceFamily
  invFun := ofFaceFamily
  left_inv := homEquiv.left_inv
  right_inv := homEquiv.right_inv

/-- Under `homEquiv`, a map to matching tuples is evaluated coordinatewise. -/
@[simp, stacks 0189 "matching tuple Hom equivalence coordinate"]
theorem homEquiv.apply {T : Type u} (f : T ⟶ Tuple U) (i : Fin (n + 2)) (t : T) :
    (homEquiv U T f).app i t = (f t).face i := sorry

/-- The inverse matching-tuple equivalence reconstructs every tuple coordinate pointwise. -/
@[simp, stacks 0189 "matching tuple Hom equivalence inverse coordinate"]
theorem homEquiv.symm_apply.face {T : Type u} (F : FaceFamily U T)
    (i : Fin (n + 2)) (t : T) :
    ((homEquiv U T).symm F t).face i = F.app i t := sorry

/-- The matching-tuple equivalence is natural under precomposition of its test type. -/
@[stacks 0189 "matching tuple equivalence naturality"]
theorem homEquiv.comp {T T' : Type u} (f : T ⟶ T') (g : T' ⟶ Tuple U) :
    homEquiv U T (f ≫ g) =
      (FaceFamily.presheaf U).map f.op (homEquiv U T' g) := sorry

/-- The explicit matching-tuple type represents the compatible face-family presheaf. -/
@[stacks 0189 "matching tuple representability"]
def representableBy (U : SSet.Truncated.{u} n) :
    (FaceFamily.presheaf U).RepresentableBy (Tuple U) where
  homEquiv := homEquiv U _
  homEquiv_comp := homEquiv.comp

namespace functor

namespace yonedaIso

/-- Naturality of the explicit tuple representations in the truncated simplicial set. -/
@[stacks 0189 "naturality of matching-tuple representations"]
theorem naturality {V : SSet.Truncated.{u} n} (α : U ⟶ V) :
    (Tuple.functor n ⋙ yoneda).map α ≫
        (Tuple.representableBy V).toIso.hom =
      (Tuple.representableBy U).toIso.hom ≫
        (FaceFamily.presheaf.functor (C := Type u) n).map α := sorry

end yonedaIso

/-- The tuple functor represents the face-family presheaf functor, naturally in the truncated
simplicial set. -/
@[stacks 0189 "natural representation by matching tuples"]
def yonedaIso (n : ℕ) :
    Tuple.functor n ⋙ yoneda ≅
      FaceFamily.presheaf.functor (C := Type u) n :=
  NatIso.ofComponents (fun U ↦ (Tuple.representableBy U).toIso)
    (fun {U V} α ↦ yonedaIso.naturality (U := U) (V := V) α)

namespace yonedaIso

/-- A component of the natural tuple representation is the canonical represented-presheaf
isomorphism. -/
@[simp, stacks 0189 "bundled component of the natural tuple representation"]
theorem app (U : SSet.Truncated.{u} n) :
    (yonedaIso n).app U = (Tuple.representableBy U).toIso := sorry

/-- The forward component of the natural tuple representation is the represented-by
isomorphism. -/
@[simp, stacks 0189 "component of the natural tuple representation"]
theorem hom_app (U : SSet.Truncated.{u} n) :
    (yonedaIso n).hom.app U = (Tuple.representableBy U).toIso.hom := sorry

/-- The inverse component of the natural tuple representation is the inverse represented-by
isomorphism. -/
@[simp, stacks 0189 "inverse component of the natural tuple representation"]
theorem inv_app (U : SSet.Truncated.{u} n) :
    (yonedaIso n).inv.app U = (Tuple.representableBy U).toIso.inv := sorry

end yonedaIso

end functor

end CategoryTheory.SimplicialObject.Truncated.matching.FaceFamily.Tuple
