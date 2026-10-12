/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Positive

/-!
@stack 0G5M

# Simplicial maps on positive endofunctor iterates

This leaf owns the face and degeneracy maps obtained from a counit-like and a
comultiplication-like natural transformation, together with their reusable simplicial
identities.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctor

/-- The face map obtained by applying `d : Y ⟶ 𝟭 C` to the factor indexed by `j`, counted from
the left. -/
@[stacks 0G5M "positive iterate face map"]
def face {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (n : ℕ) (j : Fin (n + 2)) :
    Y ⁺⦋n + 1⦌ ⟶ Y ⁺⦋n⦌ :=
  match n with
  | 0 =>
      Fin.lastCases
        (Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom)
        (fun _ ↦ Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom)
        j
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y ⁺⦋n + 1⦌) d ≫
          (Functor.rightUnitor (Y ⁺⦋n + 1⦌)).hom)
        (fun i ↦ Functor.whiskerRight (face d n i) Y)
        j

/-- The degeneracy map obtained by applying `s : Y ⟶ Y ⋙ Y` to the factor indexed by `j`,
counted from the left. -/
@[stacks 0G5M "positive iterate degeneracy map"]
def degeneracy {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y) (n : ℕ) (j : Fin (n + 1)) :
    Y ⁺⦋n⦌ ⟶ Y ⁺⦋n + 1⦌ :=
  match n with
  | 0 => s
  | n + 1 =>
      Fin.lastCases
        (Functor.whiskerLeft (Y ⁺⦋n⦌) s ≫ (Functor.associator (Y ⁺⦋n⦌) Y Y).inv)
        (fun i ↦ Functor.whiskerRight (degeneracy s n i) Y)
        j

namespace face

/-- The first degree-zero face applies the counit-like map to the left factor. -/
@[simp, stacks 0G5M "first degree-zero positive-iterate face"]
theorem zero_zero {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) :
    face d 0 (0 : Fin 2) =
      Functor.whiskerRight d Y ≫ (Functor.leftUnitor Y).hom := sorry

/-- The last degree-zero face applies the counit-like map to the right factor. -/
@[simp, stacks 0G5M "last degree-zero positive-iterate face"]
theorem zero_one {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) :
    face d 0 (1 : Fin 2) =
      Functor.whiskerLeft Y d ≫ (Functor.rightUnitor Y).hom := sorry

/-- The last face of a successor iterate applies the counit-like map to its rightmost
factor. -/
@[simp, stacks 0G5M "last face of a successor positive iterate"]
theorem succ_last {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (n : ℕ) :
    face d (n + 1) (Fin.last (n + 2)) =
      Functor.whiskerLeft (Y ⁺⦋n + 1⦌) d ≫
        (Functor.rightUnitor (Y ⁺⦋n + 1⦌)).hom := sorry

/-- Every nonlast face of a successor iterate is obtained by right-whiskering the
corresponding face of the preceding iterate. -/
@[simp, stacks 0G5M "nonlast face of a successor positive iterate"]
theorem succ_castSucc {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (n : ℕ)
    (j : Fin (n + 2)) :
    face d (n + 1) j.castSucc = Functor.whiskerRight (face d n j) Y := sorry

/-- The two degree-zero face maps agree after postcomposition with the counit-like map. -/
@[stacks 0G5M "degree-zero face compatibility"]
theorem comp_counit {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) :
    face d 0 0 ≫ d = face d 0 1 ≫ d := sorry

/-- Face maps obtained by inserting a fixed natural transformation satisfy the face-face
relation. -/
@[stacks 0G5M "face-face relation for iterated maps"]
theorem comp_face {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    face d (n + 1) j.succ ≫ face d n i =
      face d (n + 1) i.castSucc ≫ face d n j := sorry

end face

namespace degeneracy

/-- The unique degeneracy in degree zero is the displayed comultiplication-like map. -/
@[simp, stacks 0G5M "degree-zero positive-iterate degeneracy"]
theorem zero {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y) :
    degeneracy s 0 (0 : Fin 1) = s := sorry

/-- The last degeneracy of a successor iterate applies the comultiplication-like map to its
rightmost factor. -/
@[simp, stacks 0G5M "last degeneracy of a successor positive iterate"]
theorem succ_last {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y) (n : ℕ) :
    degeneracy s (n + 1) (Fin.last (n + 1)) =
      Functor.whiskerLeft (Y ⁺⦋n⦌) s ≫
        (Functor.associator (Y ⁺⦋n⦌) Y Y).inv := sorry

/-- Every nonlast degeneracy of a successor iterate is obtained by right-whiskering the
corresponding degeneracy of the preceding iterate. -/
@[simp, stacks 0G5M "nonlast degeneracy of a successor positive iterate"]
theorem succ_castSucc {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y) (n : ℕ)
    (j : Fin (n + 1)) :
    degeneracy s (n + 1) j.castSucc =
      Functor.whiskerRight (degeneracy s n j) Y := sorry

/-- A face before a nonadjacent degeneracy commutes past it in the lower-index case. -/
@[stacks 0G5M "degeneracy-face relation below the diagonal"]
theorem comp_face_of_le {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (n : ℕ)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : i ≤ j.castSucc) :
    degeneracy s (n + 1) j.succ ≫
        face d (n + 1) i.castSucc =
      face d n i ≫ degeneracy s n j := sorry

/-- A face after a nonadjacent degeneracy commutes past it in the higher-index case. -/
@[stacks 0G5M "degeneracy-face relation above the diagonal"]
theorem comp_face_of_gt {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) (n : ℕ)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hji : j.castSucc < i) :
    degeneracy s (n + 1) j.castSucc ≫
        face d (n + 1) i.succ =
      face d n i ≫ degeneracy s n j := sorry

/-- The first adjacent face cancels a degeneracy when the corresponding degree-zero counit law
holds. -/
@[stacks 0G5M "first degeneracy-face cancellation"]
theorem comp_face_castSucc {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : degeneracy s 0 0 ≫ face d 0 0 = 𝟙 Y)
    (hσδ₁ : degeneracy s 0 0 ≫ face d 0 1 = 𝟙 Y)
    (n : ℕ) (j : Fin (n + 1)) :
    degeneracy s n j ≫ face d n j.castSucc =
      𝟙 (Y ⁺⦋n⦌) := sorry

/-- The second adjacent face cancels a degeneracy when the corresponding degree-zero counit law
holds. -/
@[stacks 0G5M "second degeneracy-face cancellation"]
theorem comp_face_succ {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : degeneracy s 0 0 ≫ face d 0 0 = 𝟙 Y)
    (hσδ₁ : degeneracy s 0 0 ≫ face d 0 1 = 𝟙 Y)
    (n : ℕ) (j : Fin (n + 1)) :
    degeneracy s n j ≫ face d n j.succ =
      𝟙 (Y ⁺⦋n⦌) := sorry

/-- Degeneracy maps satisfy the degeneracy-degeneracy relation once its degree-zero
coassociativity identity holds. -/
@[stacks 0G5M "degeneracy-degeneracy relation"]
theorem comp_degeneracy {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y)
    (hσσ : degeneracy s 0 0 ≫ degeneracy s 1 0 =
      degeneracy s 0 0 ≫ degeneracy s 1 1)
    (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    degeneracy s n j ≫ degeneracy s (n + 1) i.castSucc =
      degeneracy s n i ≫ degeneracy s (n + 1) j.succ := sorry

end degeneracy

end IteratedEndofunctor

end CategoryTheory
