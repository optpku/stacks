module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Proper.ValuativeCriterion.DVR

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.11.3: let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic
stacks over a scheme `S`. Assume that `Y` is locally Noetherian, that `f` and
`h` are of finite type, that `f` is separated, and that the image of
`|h| : |U| ⟶ |X|` is dense in `|X|`. For every 2-commutative diagram
`Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a discrete valuation ring
with field of fractions `K` and the comparison is
`γ : y ∘ j ≅ f ∘ h ∘ u`, suppose there exist a field extension `K'/K` and a
valuation ring `A' ⊂ K'` dominating `A` such that the category of dotted arrows
for the induced square `Spec(K') ⟶ X` over `Spec(A') ⟶ Y`, with the induced
comparison `γ' : y' ∘ j' ≅ f ∘ x'`, is nonempty. Then `f` is proper. -/
@[stacks 0CQM] #check
  (AlgebraicGeometry.AlgebraicStack.Proper.of_existsExtensionAlong :
    ∀ {S : Scheme.{u}} {U X Y : GroupoidsOver S}
      [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) (h : U ⟶ X)
      [IsLocallyNoetherian Y] [FiniteType f] [FiniteType h] [Separated f],
      DenseRange (Points.map h) →
      ValuativeCriterion.DVR.Along.ExistsExtension h f → Proper f)

end AlgebraicGeometry.AlgebraicStack
