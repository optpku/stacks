module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.ReductionData
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement

/-!
# Quasi-compactness under completion

Completion preserves quasi-compactness of morphisms of algebraic spaces and
detects quasi-compactness for locally finite-type morphisms to locally Noetherian
algebraic spaces that are isomorphisms over the complementary open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact morphism of algebraic spaces induces a morphism of completions
along a closed subset and its inverse image that is quasi-compact on the canonical
reductions. -/
@[stacks 0GDE]
theorem quasiCompact_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.QuasiCompact f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.ReductionData.QuasiCompact
      (completionAlong.reductionData X' (T.preimage (Points.continuous_map f)))
      (completionAlong.reductionData X T) (completionAlong.map f T) :=
  sorry

/-- A locally finite-type morphism to a locally Noetherian algebraic space that
is an isomorphism over the complement of a closed subset is quasi-compact if and
only if its canonical completion map is quasi-compact on the canonical reductions. -/
@[stacks 0ARU]
theorem completionFunctor.quasiCompact_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.QuasiCompact f ↔
      FormalAlgebraicSpace.ReductionData.QuasiCompact
        (completionAlong.reductionData X' (T.preimage (Points.continuous_map f)))
        (completionAlong.reductionData X T) (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
