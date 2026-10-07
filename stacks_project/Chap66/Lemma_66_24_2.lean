module

public import stacks_project.Chap66.Lemma_66_24_2_Topology
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 66.24.2 (1): if an algebraic space `X` over a scheme `S` is locally Noetherian,
then `|X|` is a locally Noetherian topological space. -/
@[stacks 04ZF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.locallyNoetherianSpace :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [AlgebraicSpace.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicSpace.Points X))
      (_ : AlgebraicSpace.Points.OpenQuotientAtlas X τ),
      @TopologicalSpace.LocallyNoetherianSpace (AlgebraicSpace.Points X) τ)

/- Lemma 66.24.2 (2): if an algebraic space `X` over a scheme `S` is quasi-compact and
locally Noetherian, then `|X|` is a Noetherian topological space. -/
@[stacks 04ZF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.noetherianSpace :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [AlgebraicSpace.IsQuasiCompact X] [AlgebraicSpace.IsLocallyNoetherian X]
      (τ : TopologicalSpace (AlgebraicSpace.Points X))
      (_ : AlgebraicSpace.Points.OpenQuotientAtlas X τ),
      @TopologicalSpace.NoetherianSpace (AlgebraicSpace.Points X) τ)
