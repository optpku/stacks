module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 67.17.1: Let `S` be a scheme. Let `W ⊆ S` be a scheme-theoretically dense
open subscheme. Let `f : X ⟶ S` be a morphism of schemes which is flat, locally of
finite presentation, and locally quasi-finite. Then `f ⁻¹ᵁ W` is scheme-theoretically
dense in `X`. -/
@[stacks 0832] #check
  (AlgebraicGeometry.schemeTheoreticallyDense_preimage_of_flat_locallyQuasiFinite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    (W : S.Opens),
    schemeTheoreticallyDense W → schemeTheoreticallyDense (f ⁻¹ᵁ W))

end AlgebraicGeometry
