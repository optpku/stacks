module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension

/-!
# Points of maximal δ-dimension

In the good setup of Situation 82.2.1, a point of a closed subset of `|X|`
that attains the upper bound for `dim_δ` is a generic point of an irreducible
component.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.4.5: In Situation 82.2.1, let `X / B` be good. Let `T ⊂ |X|` be a
closed subset and `t ∈ T`. If `dim_δ(T) ≤ k` and `δ_{X/B}(t) = k`, then `t` is a
generic point of an irreducible component of `T`. -/
@[stacks 0EE6]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.ofIrreducibleComponent_of_closedSetDeltaDimension_le :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (T : Closeds (Points X))
    (t : Points X) (ht : t ∈ T) (k : ℤ)
    (hdim : (closedSetDeltaDimension f) δ T ≤ (k : EInt))
    (htk : (relativeDimensionFunction f) δ t = k),
    IsGenericPoint.ofIrreducibleComponent t T.carrier)

end AlgebraicGeometry.AlgebraicSpace.Hom
