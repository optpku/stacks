module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.FiniteSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.25.6: Let `S` be a scheme. Let `f : Y ⟶ X` be a surjective finite
morphism of decent and locally Noetherian algebraic spaces. Let
`δ : Points X → ℤ` be a function. If `δ ∘ Points.map f` is a dimension
function, then `δ` is a dimension function. -/
@[stacks 0ED9] #check
  (AlgebraicGeometry.AlgebraicSpace.isDimensionFunction_of_comp_map :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      [Surjective f] [IsFinite f] [IsDecent Y] [IsDecent X]
      [IsLocallyNoetherian Y] [IsLocallyNoetherian X] {δ : Points X → ℤ},
      IsDimensionFunction (δ ∘ Points.map f) → IsDimensionFunction δ)

end AlgebraicGeometry.AlgebraicSpace
