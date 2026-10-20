module

public import ReasLib.AlgebraicGeometry.Scheme.GermInjective
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.29.8 (1): an integral scheme is germ-injective. -/
@[stacks 0BX3] #check (AlgebraicGeometry.instIsGermInjectiveOfIsIntegral :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X],
    X.IsGermInjective)

/- Lemma 28.29.8 (2): a locally Noetherian scheme is germ-injective. -/
@[stacks 0BX3] #check (AlgebraicGeometry.instIsGermInjectiveOfIsLocallyNoetherian :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X],
    X.IsGermInjective)

/- Lemma 28.29.8 (3): a reduced scheme with finitely many irreducible components is
germ-injective. -/
@[stacks 0BX3] #check
  (AlgebraicGeometry.Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsReduced X]
      [Finite (irreducibleComponents X)], X.IsGermInjective)
