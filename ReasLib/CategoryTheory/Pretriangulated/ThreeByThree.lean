/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Distinguished Three-by-Three Diagrams

This leaf packages the diagrammatic data of the three-by-three lemma without
choosing any of the auxiliary octahedra used to construct it.  The data is
available in every pretriangulated category; the existence theorem is a
separate triangulated-category result.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- Stacks 05R0: the data of a distinguished three-by-three extension of a
commutative square.

The input square supplies the upper-left square.  The six distinguished
triangles, the four induced morphisms of triangles, and the signed
lower-right compatibility are retained as explicit data. -/
@[stacks 05R0]
structure ThreeByThree
    {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') where
  /-- The third vertex of the top row. -/
  topRight : C
  /-- The third vertex of the middle row. -/
  middleRight : C
  /-- The first vertex of the bottom row. -/
  bottomLeft : C
  /-- The second vertex of the bottom row. -/
  bottomMiddle : C
  /-- The third vertex of the bottom row. -/
  bottomRight : C
  /-- The second morphism of the top row. -/
  top₂ : Y ⟶ topRight
  /-- The third morphism of the top row. -/
  top₃ : topRight ⟶ X⟦(1 : ℤ)⟧
  /-- The second morphism of the middle row. -/
  middle₂ : Y' ⟶ middleRight
  /-- The third morphism of the middle row. -/
  middle₃ : middleRight ⟶ X'⟦(1 : ℤ)⟧
  /-- The second morphism of the left column. -/
  left₂ : X' ⟶ bottomLeft
  /-- The third morphism of the left column. -/
  left₃ : bottomLeft ⟶ X⟦(1 : ℤ)⟧
  /-- The second morphism of the middle column. -/
  center₂ : Y' ⟶ bottomMiddle
  /-- The third morphism of the middle column. -/
  center₃ : bottomMiddle ⟶ Y⟦(1 : ℤ)⟧
  /-- The first morphism of the right column. -/
  right₁ : topRight ⟶ middleRight
  /-- The second morphism of the right column. -/
  right₂ : middleRight ⟶ bottomRight
  /-- The third morphism of the right column. -/
  right₃ : bottomRight ⟶ topRight⟦(1 : ℤ)⟧
  /-- The first morphism of the bottom row. -/
  bottom₁ : bottomLeft ⟶ bottomMiddle
  /-- The second morphism of the bottom row. -/
  bottom₂ : bottomMiddle ⟶ bottomRight
  /-- The third morphism of the bottom row. -/
  bottom₃ : bottomRight ⟶ bottomLeft⟦(1 : ℤ)⟧
  /-- Distinguishedness of the top row. -/
  topRowMem : Triangle.mk f top₂ top₃ ∈ distTriang C
  /-- Distinguishedness of the middle row. -/
  middleRowMem : Triangle.mk f' middle₂ middle₃ ∈ distTriang C
  /-- Distinguishedness of the left column. -/
  leftColumnMem : Triangle.mk u left₂ left₃ ∈ distTriang C
  /-- Distinguishedness of the middle column. -/
  middleColumnMem : Triangle.mk v center₂ center₃ ∈ distTriang C
  /-- The top-to-middle square on the second morphisms. -/
  topToMiddle₂ : top₂ ≫ right₁ = v ≫ middle₂
  /-- The top-to-middle square on the third morphisms. -/
  topToMiddle₃ : top₃ ≫ u⟦(1 : ℤ)⟧' = right₁ ≫ middle₃
  /-- The left-to-middle square on the second morphisms. -/
  leftToMiddle₂ : left₂ ≫ bottom₁ = f' ≫ center₂
  /-- The left-to-middle square on the third morphisms. -/
  leftToMiddle₃ : left₃ ≫ f⟦(1 : ℤ)⟧' = bottom₁ ≫ center₃
  /-- Distinguishedness of the bottom row. -/
  bottomRowMem : Triangle.mk bottom₁ bottom₂ bottom₃ ∈ distTriang C
  /-- Distinguishedness of the right column. -/
  rightColumnMem : Triangle.mk right₁ right₂ right₃ ∈ distTriang C
  /-- The central square of the diagram. -/
  centerSq : CommSq middle₂ center₂ right₂ bottom₂
  /-- The square adjacent to the middle row and right column. -/
  middleRightSq : CommSq middle₃ right₂ (left₂⟦(1 : ℤ)⟧') bottom₃
  /-- The square adjacent to the bottom row and middle column. -/
  lowerMiddleSq : CommSq bottom₂ center₃ right₃ (top₂⟦(1 : ℤ)⟧')
  /-- The lower-right square anticommutes after shifting. -/
  lowerRightAnticomm : bottom₃ ≫ left₃⟦(1 : ℤ)⟧' = -(right₃ ≫ top₃⟦(1 : ℤ)⟧')

namespace ThreeByThree

variable {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
  {sq : CommSq f u v f'}

/-- Stacks 05R0: the top distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def topRow (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk f E.top₂ E.top₃

/-- Stacks 05R0: the middle distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def middleRow (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk f' E.middle₂ E.middle₃

/-- Stacks 05R0: the left distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def leftColumn (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk u E.left₂ E.left₃

/-- Stacks 05R0: the middle distinguished triangle in the column direction. -/
@[stacks 05R0]
def middleColumn (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk v E.center₂ E.center₃

/-- Stacks 05R0: the bottom distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def bottomRow (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk E.bottom₁ E.bottom₂ E.bottom₃

/-- Stacks 05R0: the right distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def rightColumn (E : ThreeByThree sq) : Triangle C :=
  Triangle.mk E.right₁ E.right₂ E.right₃

/-- The top row of a three-by-three diagram is distinguished. -/
@[simp]
theorem topRow_mem_distTriang (E : ThreeByThree sq) :
    E.topRow ∈ distTriang C := sorry

/-- The middle row of a three-by-three diagram is distinguished. -/
@[simp]
theorem middleRow_mem_distTriang (E : ThreeByThree sq) :
    E.middleRow ∈ distTriang C := sorry

/-- The left column of a three-by-three diagram is distinguished. -/
@[simp]
theorem leftColumn_mem_distTriang (E : ThreeByThree sq) :
    E.leftColumn ∈ distTriang C := sorry

/-- The middle column of a three-by-three diagram is distinguished. -/
@[simp]
theorem middleColumn_mem_distTriang (E : ThreeByThree sq) :
    E.middleColumn ∈ distTriang C := sorry

/-- The bottom row of a three-by-three diagram is distinguished. -/
@[simp]
theorem bottomRow_mem_distTriang (E : ThreeByThree sq) :
    E.bottomRow ∈ distTriang C := sorry

/-- The right column of a three-by-three diagram is distinguished. -/
@[simp]
theorem rightColumn_mem_distTriang (E : ThreeByThree sq) :
    E.rightColumn ∈ distTriang C := sorry

/-- Stacks 05R0: the vertical comparison from the top row to the middle row. -/
@[stacks 05R0]
def topToMiddle (E : ThreeByThree sq) : E.topRow ⟶ E.middleRow :=
  Triangle.homMk _ _ u v E.right₁ sq.w E.topToMiddle₂ E.topToMiddle₃

/-- The first component of `topToMiddle` is the left edge of the input square. -/
@[simp]
theorem topToMiddle_hom₁ (E : ThreeByThree sq) : (E.topToMiddle).hom₁ = u := sorry

/-- The second component of `topToMiddle` is the right edge of the input square. -/
@[simp]
theorem topToMiddle_hom₂ (E : ThreeByThree sq) : (E.topToMiddle).hom₂ = v := sorry

/-- The third component of `topToMiddle` is the first edge of the right column. -/
@[simp]
theorem topToMiddle_hom₃ (E : ThreeByThree sq) : (E.topToMiddle).hom₃ = E.right₁ := sorry

/-- Stacks 05R0: the vertical comparison from the middle row to the bottom row. -/
@[stacks 05R0]
def middleToBottom (E : ThreeByThree sq) : E.middleRow ⟶ E.bottomRow :=
  Triangle.homMk _ _ E.left₂ E.center₂ E.right₂ E.leftToMiddle₂.symm E.centerSq.w
    E.middleRightSq.w

/-- The first component of `middleToBottom` is the second edge of the left column. -/
@[simp]
theorem middleToBottom_hom₁ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₁ = E.left₂ := sorry

/-- The second component of `middleToBottom` is the second edge of the middle column. -/
@[simp]
theorem middleToBottom_hom₂ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₂ = E.center₂ := sorry

/-- The third component of `middleToBottom` is the second edge of the right column. -/
@[simp]
theorem middleToBottom_hom₃ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₃ = E.right₂ := sorry

/-- Stacks 05R0: the horizontal comparison from the left column to the middle column. -/
@[stacks 05R0]
def leftToMiddle (E : ThreeByThree sq) : E.leftColumn ⟶ E.middleColumn :=
  Triangle.homMk _ _ f f' E.bottom₁ sq.w.symm E.leftToMiddle₂ E.leftToMiddle₃

/-- The first component of `leftToMiddle` is the top edge of the input square. -/
@[simp]
theorem leftToMiddle_hom₁ (E : ThreeByThree sq) : (E.leftToMiddle).hom₁ = f := sorry

/-- The second component of `leftToMiddle` is the bottom edge of the input square. -/
@[simp]
theorem leftToMiddle_hom₂ (E : ThreeByThree sq) : (E.leftToMiddle).hom₂ = f' := sorry

/-- The third component of `leftToMiddle` is the first edge of the bottom row. -/
@[simp]
theorem leftToMiddle_hom₃ (E : ThreeByThree sq) :
    (E.leftToMiddle).hom₃ = E.bottom₁ := sorry

/-- Stacks 05R0: the horizontal comparison from the middle column to the right column. -/
@[stacks 05R0]
def middleToRight (E : ThreeByThree sq) : E.middleColumn ⟶ E.rightColumn :=
  Triangle.homMk _ _ E.top₂ E.middle₂ E.bottom₂ E.topToMiddle₂.symm E.centerSq.w.symm
    E.lowerMiddleSq.w.symm

/-- The first component of `middleToRight` is the second edge of the top row. -/
@[simp]
theorem middleToRight_hom₁ (E : ThreeByThree sq) :
    (E.middleToRight).hom₁ = E.top₂ := sorry

/-- The second component of `middleToRight` is the second edge of the middle row. -/
@[simp]
theorem middleToRight_hom₂ (E : ThreeByThree sq) :
    (E.middleToRight).hom₂ = E.middle₂ := sorry

/-- The third component of `middleToRight` is the second edge of the bottom row. -/
@[simp]
theorem middleToRight_hom₃ (E : ThreeByThree sq) :
    (E.middleToRight).hom₃ = E.bottom₂ := sorry

/-- Stacks 05R0: every commutative square in a triangulated category admits a distinguished
three-by-three extension. -/
@[stacks 05R0]
theorem nonempty_of_commSq [IsTriangulated C] (sq : CommSq f u v f') :
    Nonempty (ThreeByThree sq) := sorry

/-- Stacks 05R0: equation form of `nonempty_of_commSq`. -/
@[stacks 05R0]
theorem nonempty_of_comm [IsTriangulated C] (comm : f ≫ v = u ≫ f') :
    Nonempty (ThreeByThree (CommSq.mk comm)) := sorry

end ThreeByThree

end CategoryTheory.Pretriangulated
