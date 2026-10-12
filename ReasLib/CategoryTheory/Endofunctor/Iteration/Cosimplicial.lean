/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Positive

/-!
# Cosimplicial maps on positive endofunctor iterates

This leaf owns the iterated point together with the coface and codegeneracy maps obtained from a
point and a multiplication-like natural transformation, including their reusable cosimplicial
identities.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctor

namespace point

/-- Iterating a point `η : 𝟭 C ⟶ Y` at an object is the canonical coalgebra unfold into each
positive iterate of `Y`. -/
@[stacks 0G5M "component of an iterated endofunctor point"]
def component {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) :
    (n : ℕ) → (X : C) → X ⟶ (Y ⁺⦋n⦌).obj X :=
  fun n X ↦ Endofunctor.iterate.unfold Y (η.app X) (n + 1)

/-- The first component of an iterated point is the original point. -/
@[simp, stacks 0G5M "first component of an iterated endofunctor point"]
theorem component_zero {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (X : C) :
    component η 0 X = η.app X := sorry

/-- A successor component adds the point at the preceding positive iterate. -/
@[simp, stacks 0G5M "successor component of an iterated endofunctor point"]
theorem component_succ {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) (X : C) :
    component η (n + 1) X =
      component η n X ≫ η.app ((Y ⁺⦋n⦌).obj X) := sorry

/-- Components of an iterated point are natural in the object. -/
@[stacks 0G5M "naturality of an iterated endofunctor point"]
theorem component_naturality {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ)
    {X X' : C} (f : X ⟶ X') :
    f ≫ component η n X' = component η n X ≫ (Y ⁺⦋n⦌).map f := sorry

/-- The iterated-point component is the zero-based coalgebra unfold starting at `X`. -/
@[stacks 0G5M "iterated point as endofunctor unfolding"]
theorem component_eq_unfold {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) (X : C) :
    component η n X = Endofunctor.iterate.unfold Y (η.app X) (n + 1) := sorry

end point

/-- The coface obtained by inserting `η : 𝟭 C ⟶ Y` into one factor of a positive
iterate. -/
@[stacks 0G5N "positive iterate coface map"]
def coface {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) (j : Fin (n + 2)) :
    Y ⁺⦋n⦌ ⟶ Y ⁺⦋n + 1⦌ :=
  match n with
  | 0 =>
      Fin.lastCases
        ((Functor.rightUnitor Y).inv ≫ Functor.whiskerLeft Y η)
        (fun _ ↦ (Functor.leftUnitor Y).inv ≫ Functor.whiskerRight η Y)
        j
  | n + 1 =>
      Fin.lastCases
        ((Functor.rightUnitor (Y ⁺⦋n + 1⦌)).inv ≫
          Functor.whiskerLeft (Y ⁺⦋n + 1⦌) η)
        (fun i ↦ Functor.whiskerRight (coface η n i) Y)
        j

/-- The codegeneracy obtained by multiplying two adjacent factors of a positive iterate. -/
@[stacks 0G5N "positive iterate codegeneracy map"]
def codegeneracy {Y : C ⥤ C} (μ : Y ⋙ Y ⟶ Y) (n : ℕ) (j : Fin (n + 1)) :
    Y ⁺⦋n + 1⦌ ⟶ Y ⁺⦋n⦌ :=
  match n with
  | 0 => μ
  | n + 1 =>
      Fin.lastCases
        ((Functor.associator (Y ⁺⦋n⦌) Y Y).hom ≫
          Functor.whiskerLeft (Y ⁺⦋n⦌) μ)
        (fun i ↦ Functor.whiskerRight (codegeneracy μ n i) Y)
        j

namespace coface

/-- The first degree-zero coface inserts the point into the left factor. -/
@[simp, stacks 0G5N "first degree-zero positive-iterate coface"]
theorem zero_zero {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) :
    coface η 0 (0 : Fin 2) =
      (Functor.leftUnitor Y).inv ≫ Functor.whiskerRight η Y := sorry

/-- The last degree-zero coface inserts the point into the right factor. -/
@[simp, stacks 0G5N "last degree-zero positive-iterate coface"]
theorem zero_one {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) :
    coface η 0 (1 : Fin 2) =
      (Functor.rightUnitor Y).inv ≫ Functor.whiskerLeft Y η := sorry

/-- The last coface of a successor iterate inserts the point after its rightmost factor. -/
@[simp, stacks 0G5N "last coface of a successor positive iterate"]
theorem succ_last {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) :
    coface η (n + 1) (Fin.last (n + 2)) =
      (Functor.rightUnitor (Y ⁺⦋n + 1⦌)).inv ≫
        Functor.whiskerLeft (Y ⁺⦋n + 1⦌) η := sorry

/-- Every nonlast coface of a successor iterate is obtained by right-whiskering the
corresponding coface of the preceding iterate. -/
@[simp, stacks 0G5N "nonlast coface of a successor positive iterate"]
theorem succ_castSucc {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ)
    (j : Fin (n + 2)) :
    coface η (n + 1) j.castSucc =
      Functor.whiskerRight (coface η n j) Y := sorry

/-- The two degree-zero cofaces agree after precomposition with the unit-like map. -/
@[stacks 0G5N "degree-zero coface compatibility"]
theorem unit_comp {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) :
    η ≫ coface η 0 0 = η ≫ coface η 0 1 := sorry

/-- Cofaces obtained by inserting a fixed natural transformation satisfy the coface-coface
relation. -/
@[stacks 0G5N "coface-coface relation for iterated maps"]
theorem comp_coface {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ)
    {i j : Fin (n + 2)} (hij : i ≤ j) :
    coface η n i ≫ coface η (n + 1) j.succ =
      coface η n j ≫ coface η (n + 1) i.castSucc := sorry

end coface

namespace codegeneracy

/-- The unique codegeneracy in degree zero is the displayed multiplication-like map. -/
@[simp, stacks 0G5N "degree-zero positive-iterate codegeneracy"]
theorem zero {Y : C ⥤ C} (μ : Y ⋙ Y ⟶ Y) :
    codegeneracy μ 0 (0 : Fin 1) = μ := sorry

/-- The last codegeneracy of a successor iterate multiplies its two rightmost factors. -/
@[simp, stacks 0G5N "last codegeneracy of a successor positive iterate"]
theorem succ_last {Y : C ⥤ C} (μ : Y ⋙ Y ⟶ Y) (n : ℕ) :
    codegeneracy μ (n + 1) (Fin.last (n + 1)) =
      (Functor.associator (Y ⁺⦋n⦌) Y Y).hom ≫
        Functor.whiskerLeft (Y ⁺⦋n⦌) μ := sorry

/-- Every nonlast codegeneracy of a successor iterate is obtained by right-whiskering the
corresponding codegeneracy of the preceding iterate. -/
@[simp, stacks 0G5N "nonlast codegeneracy of a successor positive iterate"]
theorem succ_castSucc {Y : C ⥤ C} (μ : Y ⋙ Y ⟶ Y) (n : ℕ)
    (j : Fin (n + 1)) :
    codegeneracy μ (n + 1) j.castSucc =
      Functor.whiskerRight (codegeneracy μ n j) Y := sorry

/-- A coface before a nonadjacent codegeneracy commutes past it in the lower-index case. -/
@[stacks 0G5N "coface-codegeneracy relation below the diagonal"]
theorem coface_comp_of_le {Y : C ⥤ C}
    (η : 𝟭 C ⟶ Y) (μ : Y ⋙ Y ⟶ Y) (n : ℕ)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hij : i ≤ j.castSucc) :
    coface η (n + 1) i.castSucc ≫ codegeneracy μ (n + 1) j.succ =
      codegeneracy μ n j ≫ coface η n i := sorry

/-- A coface after a nonadjacent codegeneracy commutes past it in the higher-index case. -/
@[stacks 0G5N "coface-codegeneracy relation above the diagonal"]
theorem coface_comp_of_gt {Y : C ⥤ C}
    (η : 𝟭 C ⟶ Y) (μ : Y ⋙ Y ⟶ Y) (n : ℕ)
    {i : Fin (n + 2)} {j : Fin (n + 1)} (hji : j.castSucc < i) :
    coface η (n + 1) i.succ ≫ codegeneracy μ (n + 1) j.castSucc =
      codegeneracy μ n j ≫ coface η n i := sorry

/-- The first adjacent codegeneracy cancels a coface when the two degree-zero unit laws hold. -/
@[stacks 0G5N "first coface-codegeneracy cancellation"]
theorem coface_comp_castSucc {Y : C ⥤ C}
    (η : 𝟭 C ⟶ Y) (μ : Y ⋙ Y ⟶ Y)
    (hδσ₀ : coface η 0 0 ≫ codegeneracy μ 0 0 = 𝟙 Y)
    (hδσ₁ : coface η 0 1 ≫ codegeneracy μ 0 0 = 𝟙 Y)
    (n : ℕ) (j : Fin (n + 1)) :
    coface η n j.castSucc ≫ codegeneracy μ n j =
      𝟙 (Y ⁺⦋n⦌) := sorry

/-- The second adjacent codegeneracy cancels a coface when the two degree-zero unit laws hold. -/
@[stacks 0G5N "second coface-codegeneracy cancellation"]
theorem coface_comp_succ {Y : C ⥤ C}
    (η : 𝟭 C ⟶ Y) (μ : Y ⋙ Y ⟶ Y)
    (hδσ₀ : coface η 0 0 ≫ codegeneracy μ 0 0 = 𝟙 Y)
    (hδσ₁ : coface η 0 1 ≫ codegeneracy μ 0 0 = 𝟙 Y)
    (n : ℕ) (j : Fin (n + 1)) :
    coface η n j.succ ≫ codegeneracy μ n j =
      𝟙 (Y ⁺⦋n⦌) := sorry

/-- Codegeneracy maps satisfy the codegeneracy-codegeneracy relation once its degree-zero
associativity identity holds. -/
@[stacks 0G5N "codegeneracy-codegeneracy relation"]
theorem comp_codegeneracy {Y : C ⥤ C} (μ : Y ⋙ Y ⟶ Y)
    (hσσ : codegeneracy μ 1 0 ≫ codegeneracy μ 0 0 =
      codegeneracy μ 1 1 ≫ codegeneracy μ 0 0)
    (n : ℕ) {i j : Fin (n + 1)} (hij : i ≤ j) :
    codegeneracy μ (n + 1) i.castSucc ≫ codegeneracy μ n j =
      codegeneracy μ (n + 1) j.succ ≫ codegeneracy μ n i := sorry

end codegeneracy

/-- A point of an endofunctor iterates to a natural transformation from the identity functor to
each positive iterate. -/
@[stacks 0G5M "iterated point of an endofunctor"]
def point {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) : 𝟭 C ⟶ Y ⁺⦋n⦌ where
  app X := point.component η n X
  naturality _ _ f := point.component_naturality η n f

/-- The component of the bundled iterated point is its component-first construction. -/
@[simp, stacks 0G5M "component formula for an iterated endofunctor point"]
theorem point.app {Y : C ⥤ C} (η : 𝟭 C ⟶ Y) (n : ℕ) (X : C) :
    (point η n).app X = point.component η n X := sorry

end IteratedEndofunctor

end CategoryTheory
