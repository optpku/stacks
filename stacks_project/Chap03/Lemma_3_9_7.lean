module

public import stacks_project.Chap03.Lemma_3_9_4_Size
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Lemma 3.9.7. If `f : X ⟶ S` is locally of finite type and `X` is quasi-compact, then
`X.size ≤ S.size`. -/
@[stacks 04T7]
theorem size_le_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] :
    X.size ≤ S.size := sorry

end AlgebraicGeometry.Scheme
