/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula.ClosedEmbedding
import StacksCheckRecall

@[expose] public section

/-!
# Projection formula for closed embeddings

The canonical derived tensor, adjunction mate, and closed-embedding criterion are maintained in
`ReasLib`; this chapter file records the source statement.
-/

/- Lemma 20.54.4: if a morphism of ringed spaces `f : X ⟶ Y` identifies `X`
homeomorphically with a closed subset of `Y`, then for `K ∈ D(𝒪_Y)` and `E ∈ D(𝒪_X)` the
canonical morphism `R(f)_* E ⊗ᴸ K ⟶ R(f)_* (E ⊗ᴸ L(f)^* K)` is an isomorphism. -/
@[stacks 0B55]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedEmbedding.isIso_projectionFormula
