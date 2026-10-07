module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Differentials
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Lemma 40.4.1 (1): for a groupoid scheme, the canonical morphism
`t^* C_{U/R} ⟶ Ω_{R/U}` is an epimorphism. -/
@[stacks 04R9] #check
  (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison_epi :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      CategoryTheory.Epi
        (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison G))

/- Lemma 40.4.1 (2): if the source map is flat, the canonical morphism
`t^* C_{U/R} ⟶ Ω_{R/U}` is an isomorphism. -/
@[stacks 04R9] #check
  (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.Flat G.s.left],
      CategoryTheory.IsIso
        (AlgebraicGeometry.GroupoidScheme.Differentials.conormalComparison G))
