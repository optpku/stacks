module

public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Lemma_82_4_4_GenericPoint

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

/-- Lemma 82.4.5: In Situation 82.2.1, let `X / B` be good. Let `T ⊂ |X|` be a
closed subset and `t ∈ T`. If `dim_δ(T) ≤ k` and `δ_{X/B}(t) = k`, then `t` is a
generic point of an irreducible component of `T`. -/
@[stacks 0EE6]
theorem ofIrreducibleComponent_of_closedSetDeltaDimension_le
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (T : Closeds (Points X))
    (t : Points X) (ht : t ∈ T) (k : ℤ)
    (hdim : f.closedSetDeltaDimension δ T ≤ (k : EInt))
    (htk : f.relativeDimensionFunction δ t = k) :
    IsGenericPoint.ofIrreducibleComponent t T.carrier := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
