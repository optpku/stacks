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

namespace ThreeByThree

/-- The objects and morphisms completing the boundary of a three-by-three diagram.
No commutativity or distinguishedness is required to assemble its rows and columns. -/
structure Grid
    {X Y X' Y' : C} (f : X ⟶ Y) (u : X ⟶ X') (v : Y ⟶ Y') (f' : X' ⟶ Y') where
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

namespace Grid

variable {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}

/-- The top row. -/
def row₁ (G : Grid f u v f') : Triangle C := Triangle.mk f G.top₂ G.top₃

/-- The middle row. -/
def row₂ (G : Grid f u v f') : Triangle C := Triangle.mk f' G.middle₂ G.middle₃

/-- The bottom row. -/
def row₃ (G : Grid f u v f') : Triangle C :=
  Triangle.mk G.bottom₁ G.bottom₂ G.bottom₃

/-- The left column. -/
def col₁ (G : Grid f u v f') : Triangle C := Triangle.mk u G.left₂ G.left₃

/-- The middle column. -/
def col₂ (G : Grid f u v f') : Triangle C := Triangle.mk v G.center₂ G.center₃

/-- The right column. -/
def col₃ (G : Grid f u v f') : Triangle C :=
  Triangle.mk G.right₁ G.right₂ G.right₃

/-- The six distinguished triangles and the seven commuting squares and one
anticommuting square in a three-by-three diagram, apart from the input square. -/
structure IsValid (G : Grid f u v f') : Prop where
  /-- Distinguishedness of the top row. -/
  topRowMem : G.row₁ ∈ distTriang C
  /-- Distinguishedness of the middle row. -/
  middleRowMem : G.row₂ ∈ distTriang C
  /-- Distinguishedness of the left column. -/
  leftColumnMem : G.col₁ ∈ distTriang C
  /-- Distinguishedness of the middle column. -/
  middleColumnMem : G.col₂ ∈ distTriang C
  /-- The top-to-middle square on the second morphisms. -/
  topToMiddle₂ : G.top₂ ≫ G.right₁ = v ≫ G.middle₂
  /-- The top-to-middle square on the third morphisms. -/
  topToMiddle₃ : G.top₃ ≫ u⟦(1 : ℤ)⟧' = G.right₁ ≫ G.middle₃
  /-- The left-to-middle square on the second morphisms. -/
  leftToMiddle₂ : G.left₂ ≫ G.bottom₁ = f' ≫ G.center₂
  /-- The left-to-middle square on the third morphisms. -/
  leftToMiddle₃ : G.left₃ ≫ f⟦(1 : ℤ)⟧' = G.bottom₁ ≫ G.center₃
  /-- Distinguishedness of the bottom row. -/
  bottomRowMem : G.row₃ ∈ distTriang C
  /-- Distinguishedness of the right column. -/
  rightColumnMem : G.col₃ ∈ distTriang C
  /-- The central square of the diagram. -/
  centerSq : CommSq G.middle₂ G.center₂ G.right₂ G.bottom₂
  /-- The square adjacent to the middle row and right column. -/
  middleRightSq : CommSq G.middle₃ G.right₂ (G.left₂⟦(1 : ℤ)⟧') G.bottom₃
  /-- The square adjacent to the bottom row and middle column. -/
  lowerMiddleSq : CommSq G.bottom₂ G.center₃ G.right₃ (G.top₂⟦(1 : ℤ)⟧')
  /-- The lower-right square anticommutes after shifting. -/
  lowerRightAnticomm : G.bottom₃ ≫ G.left₃⟦(1 : ℤ)⟧' = -(G.right₃ ≫ G.top₃⟦(1 : ℤ)⟧')

end Grid

end ThreeByThree

/-- Stacks 05R0: a three-by-three extension of a commutative square, consisting
of a pure grid and proofs of its distinguishedness and signed compatibilities. -/
@[stacks 05R0]
structure ThreeByThree
    {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') where
  /-- The pure objects and morphisms of the diagram. -/
  toGrid : ThreeByThree.Grid f u v f'
  /-- The distinguished triangles and signed square compatibilities of the grid. -/
  isValid : toGrid.IsValid

namespace ThreeByThree

variable {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
  {sq : CommSq f u v f'}

/-- Compatibility accessor for the underlying grid data. -/
abbrev topRight (E : ThreeByThree sq) := E.toGrid.topRight

/-- Compatibility accessor for the underlying grid data. -/
abbrev middleRight (E : ThreeByThree sq) := E.toGrid.middleRight

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottomLeft (E : ThreeByThree sq) := E.toGrid.bottomLeft

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottomMiddle (E : ThreeByThree sq) := E.toGrid.bottomMiddle

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottomRight (E : ThreeByThree sq) := E.toGrid.bottomRight

/-- Compatibility accessor for the underlying grid data. -/
abbrev top₂ (E : ThreeByThree sq) := E.toGrid.top₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev top₃ (E : ThreeByThree sq) := E.toGrid.top₃

/-- Compatibility accessor for the underlying grid data. -/
abbrev middle₂ (E : ThreeByThree sq) := E.toGrid.middle₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev middle₃ (E : ThreeByThree sq) := E.toGrid.middle₃

/-- Compatibility accessor for the underlying grid data. -/
abbrev left₂ (E : ThreeByThree sq) := E.toGrid.left₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev left₃ (E : ThreeByThree sq) := E.toGrid.left₃

/-- Compatibility accessor for the underlying grid data. -/
abbrev center₂ (E : ThreeByThree sq) := E.toGrid.center₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev center₃ (E : ThreeByThree sq) := E.toGrid.center₃

/-- Compatibility accessor for the underlying grid data. -/
abbrev right₁ (E : ThreeByThree sq) := E.toGrid.right₁

/-- Compatibility accessor for the underlying grid data. -/
abbrev right₂ (E : ThreeByThree sq) := E.toGrid.right₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev right₃ (E : ThreeByThree sq) := E.toGrid.right₃

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottom₁ (E : ThreeByThree sq) := E.toGrid.bottom₁

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottom₂ (E : ThreeByThree sq) := E.toGrid.bottom₂

/-- Compatibility accessor for the underlying grid data. -/
abbrev bottom₃ (E : ThreeByThree sq) := E.toGrid.bottom₃

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev topRowMem (E : ThreeByThree sq) := E.isValid.topRowMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev middleRowMem (E : ThreeByThree sq) := E.isValid.middleRowMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev leftColumnMem (E : ThreeByThree sq) := E.isValid.leftColumnMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev middleColumnMem (E : ThreeByThree sq) := E.isValid.middleColumnMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev topToMiddle₂ (E : ThreeByThree sq) := E.isValid.topToMiddle₂

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev topToMiddle₃ (E : ThreeByThree sq) := E.isValid.topToMiddle₃

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev leftToMiddle₂ (E : ThreeByThree sq) := E.isValid.leftToMiddle₂

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev leftToMiddle₃ (E : ThreeByThree sq) := E.isValid.leftToMiddle₃

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev bottomRowMem (E : ThreeByThree sq) := E.isValid.bottomRowMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev rightColumnMem (E : ThreeByThree sq) := E.isValid.rightColumnMem

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev centerSq (E : ThreeByThree sq) := E.isValid.centerSq

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev middleRightSq (E : ThreeByThree sq) := E.isValid.middleRightSq

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev lowerMiddleSq (E : ThreeByThree sq) := E.isValid.lowerMiddleSq

/-- Compatibility accessor for the validity of the underlying grid. -/
abbrev lowerRightAnticomm (E : ThreeByThree sq) := E.isValid.lowerRightAnticomm

/-- Stacks 05R0: the top distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def topRow (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.row₁

/-- Stacks 05R0: the middle distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def middleRow (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.row₂

/-- Stacks 05R0: the left distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def leftColumn (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.col₁

/-- Stacks 05R0: the middle distinguished triangle in the column direction. -/
@[stacks 05R0]
def middleColumn (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.col₂

/-- Stacks 05R0: the bottom distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def bottomRow (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.row₃

/-- Stacks 05R0: the right distinguished triangle in a three-by-three diagram. -/
@[stacks 05R0]
def rightColumn (E : ThreeByThree sq) : Triangle C :=
  E.toGrid.col₃

/-- The top row of a three-by-three diagram is distinguished. -/
@[simp]
theorem topRow_mem_distTriang (E : ThreeByThree sq) :
    E.topRow ∈ distTriang C := E.topRowMem

/-- The middle row of a three-by-three diagram is distinguished. -/
@[simp]
theorem middleRow_mem_distTriang (E : ThreeByThree sq) :
    E.middleRow ∈ distTriang C := E.middleRowMem

/-- The left column of a three-by-three diagram is distinguished. -/
@[simp]
theorem leftColumn_mem_distTriang (E : ThreeByThree sq) :
    E.leftColumn ∈ distTriang C := E.leftColumnMem

/-- The middle column of a three-by-three diagram is distinguished. -/
@[simp]
theorem middleColumn_mem_distTriang (E : ThreeByThree sq) :
    E.middleColumn ∈ distTriang C := E.middleColumnMem

/-- The bottom row of a three-by-three diagram is distinguished. -/
@[simp]
theorem bottomRow_mem_distTriang (E : ThreeByThree sq) :
    E.bottomRow ∈ distTriang C := E.bottomRowMem

/-- The right column of a three-by-three diagram is distinguished. -/
@[simp]
theorem rightColumn_mem_distTriang (E : ThreeByThree sq) :
    E.rightColumn ∈ distTriang C := E.rightColumnMem

/-- Stacks 05R0: the vertical comparison from the top row to the middle row. -/
@[stacks 05R0]
def topToMiddle (E : ThreeByThree sq) : E.topRow ⟶ E.middleRow :=
  Triangle.homMk _ _ u v E.right₁ sq.w E.topToMiddle₂ E.topToMiddle₃

/-- The first component of `topToMiddle` is the left edge of the input square. -/
@[simp]
theorem topToMiddle_hom₁ (E : ThreeByThree sq) : (E.topToMiddle).hom₁ = u := rfl

/-- The second component of `topToMiddle` is the right edge of the input square. -/
@[simp]
theorem topToMiddle_hom₂ (E : ThreeByThree sq) : (E.topToMiddle).hom₂ = v := rfl

/-- The third component of `topToMiddle` is the first edge of the right column. -/
@[simp]
theorem topToMiddle_hom₃ (E : ThreeByThree sq) : (E.topToMiddle).hom₃ = E.right₁ := rfl

/-- Stacks 05R0: the vertical comparison from the middle row to the bottom row. -/
@[stacks 05R0]
def middleToBottom (E : ThreeByThree sq) : E.middleRow ⟶ E.bottomRow :=
  Triangle.homMk _ _ E.left₂ E.center₂ E.right₂ E.leftToMiddle₂.symm E.centerSq.w
    E.middleRightSq.w

/-- The first component of `middleToBottom` is the second edge of the left column. -/
@[simp]
theorem middleToBottom_hom₁ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₁ = E.left₂ := rfl

/-- The second component of `middleToBottom` is the second edge of the middle column. -/
@[simp]
theorem middleToBottom_hom₂ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₂ = E.center₂ := rfl

/-- The third component of `middleToBottom` is the second edge of the right column. -/
@[simp]
theorem middleToBottom_hom₃ (E : ThreeByThree sq) :
    (E.middleToBottom).hom₃ = E.right₂ := rfl

/-- Stacks 05R0: the horizontal comparison from the left column to the middle column. -/
@[stacks 05R0]
def leftToMiddle (E : ThreeByThree sq) : E.leftColumn ⟶ E.middleColumn :=
  Triangle.homMk _ _ f f' E.bottom₁ sq.w.symm E.leftToMiddle₂ E.leftToMiddle₃

/-- The first component of `leftToMiddle` is the top edge of the input square. -/
@[simp]
theorem leftToMiddle_hom₁ (E : ThreeByThree sq) : (E.leftToMiddle).hom₁ = f := rfl

/-- The second component of `leftToMiddle` is the bottom edge of the input square. -/
@[simp]
theorem leftToMiddle_hom₂ (E : ThreeByThree sq) : (E.leftToMiddle).hom₂ = f' := rfl

/-- The third component of `leftToMiddle` is the first edge of the bottom row. -/
@[simp]
theorem leftToMiddle_hom₃ (E : ThreeByThree sq) :
    (E.leftToMiddle).hom₃ = E.bottom₁ := rfl

/-- Stacks 05R0: the horizontal comparison from the middle column to the right column. -/
@[stacks 05R0]
def middleToRight (E : ThreeByThree sq) : E.middleColumn ⟶ E.rightColumn :=
  Triangle.homMk _ _ E.top₂ E.middle₂ E.bottom₂ E.topToMiddle₂.symm E.centerSq.w.symm
    E.lowerMiddleSq.w.symm

/-- The first component of `middleToRight` is the second edge of the top row. -/
@[simp]
theorem middleToRight_hom₁ (E : ThreeByThree sq) :
    (E.middleToRight).hom₁ = E.top₂ := rfl

/-- The second component of `middleToRight` is the second edge of the middle row. -/
@[simp]
theorem middleToRight_hom₂ (E : ThreeByThree sq) :
    (E.middleToRight).hom₂ = E.middle₂ := rfl

/-- The third component of `middleToRight` is the second edge of the bottom row. -/
@[simp]
theorem middleToRight_hom₃ (E : ThreeByThree sq) :
    (E.middleToRight).hom₃ = E.bottom₂ := rfl

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
