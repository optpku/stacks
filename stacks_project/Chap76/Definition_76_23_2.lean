/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_23_2_FlatOnFiber
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.23.2 (1): Let `S` be a scheme. Let `X ⟶ Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Let `x ∈ |X|`
be a point and denote `z ∈ |Z|` its image `Points.map (f ≫ h) x`. The restriction
of `F` to its fibre over `z` is flat at `x` over the fibre of `Y` over `z` if the
equivalent conditions of Lemma 76.23.1 are satisfied. -/
@[stacks 05WZ] #check
  (Modules.flatOnFiberAt :
    {S : Scheme.{u}} → {X Y Z : AlgebraicSpace S} →
      X.Modules → (X ⟶ Y) → (Y ⟶ Z) → Points X → Prop)

/- Definition 76.23.2 (2): Let `S` be a scheme. Let `X ⟶ Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `x ∈ |X|` be a point and denote `z ∈ |Z|` its image
`Points.map (f ≫ h) x`. The fibre of `X` over `z` is flat at `x` over the fibre of
`Y` over `z` if the equivalent conditions of Lemma 76.23.1 hold with `F = 𝒪_X`. -/
@[stacks 05WZ] #check
  (fiberFlatAt :
    {S : Scheme.{u}} → {X Y Z : AlgebraicSpace S} →
      (X ⟶ Y) → (Y ⟶ Z) → Points X → Prop)

/- Definition 76.23.2 (3): Let `S` be a scheme. Let `X ⟶ Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `z ∈ |Z|`. The fibre of `X` over `z` is flat over
the fibre of `Y` over `z` if for all `x ∈ |X|` lying over `z` the fibre of `X`
over `z` is flat at `x` over the fibre of `Y` over `z`. -/
@[stacks 05WZ] #check
  (fiberFlatOver :
    {S : Scheme.{u}} → {X Y Z : AlgebraicSpace S} →
      (X ⟶ Y) → (Y ⟶ Z) → Points Z → Prop)
