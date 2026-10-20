module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- 68.18.0.2: consider a cartesian square `W ⟶ Z` over `X ⟶ Y` of algebraic spaces over a
scheme `S`, with maps `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`. Let
`x ∈ |X|` and `z ∈ |Z|` map to the same point of `|Y|`. The fibre is the set
`F_{x, z} = { w ∈ |W| | Points.map p w = x ∧ Points.map q w = z }`. -/
@[stacks 0AC2] #check (AlgebraicGeometry.AlgebraicSpace.Points.fibre :
  ∀ {S : Scheme.{u}} {W X Z : AlgebraicSpace S},
    (W ⟶ X) → (W ⟶ Z) → Points X → Points Z → Set (Points W))
