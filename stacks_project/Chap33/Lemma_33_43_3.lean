module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.43.3: let `X` be a separated finite-type scheme over a field `k`. If
`topologicalKrullDim X ≤ 1`, then its structure morphism
`f : X ⟶ Spec (CommRingCat.of k)` is H-quasi-projective. -/
@[stacks 0A25] #check
  (AlgebraicGeometry.HQuasiProjective.of_dimension_le_one :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
      [Scheme.Hom.FiniteType f] [IsSeparated f],
      topologicalKrullDim X ≤ 1 → HQuasiProjective f)
