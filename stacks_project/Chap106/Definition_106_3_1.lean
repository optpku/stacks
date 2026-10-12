/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap106.Definition_106_3_1_Hom
public import stacks_project.Chap106.Definition_106_3_1_Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Definition 106.3.1 (1): an algebraic stack `X'` is a thickening of an
algebraic stack `X` if `X` is a closed substack of `X'` and the associated
topological spaces are equal. -/
@[stacks 0BPP] #check (IsThickening :
  {S : Scheme.{u}} → {X X' : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] → (X ⟶ X') → Prop)

/- Definition 106.3.1 (2): a morphism of thickenings is a pair `(f, f')` with
`f' : X' ⟶ Y'` whose restriction to `X` factors through `Y`. -/
@[stacks 0BPP] #check (IsThickening.Hom.mk :
  {S : Scheme.{u}} → {X X' Y Y' : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] →
      [AlgebraicStack Y] → [AlgebraicStack Y'] →
        (i : X ⟶ X') → (j : Y ⟶ Y') →
          [IsThickening i] → [IsThickening j] →
            (f : X ⟶ Y) → (f' : X' ⟶ Y') →
              (f ≫ j ≅ i ≫ f') → IsThickening.Hom i j f f')

/- Definition 106.3.1 (3): thickenings over an algebraic stack `Z` and morphisms
of thickenings over `Z` equip the ambients with structure morphisms to `Z` so
that `f'` fits in a 2-commutative diagram. -/
@[stacks 0BPP] #check (IsThickening.HomOver.mk :
  {S : Scheme.{u}} → {X X' Y Y' Z : GroupoidsOver S} →
    [AlgebraicStack X] → [AlgebraicStack X'] →
      [AlgebraicStack Y] → [AlgebraicStack Y'] → [AlgebraicStack Z] →
        (i : X ⟶ X') → (j : Y ⟶ Y') →
          [IsThickening i] → [IsThickening j] →
            (pX' : X' ⟶ Z) → (pY' : Y' ⟶ Z) →
              (f : X ⟶ Y) → (f' : X' ⟶ Y') →
                (f ≫ j ≅ i ≫ f') → (f' ≫ pY' ≅ pX') →
                  IsThickening.HomOver i j pX' pY' f f')
