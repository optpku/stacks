module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteAbove
import StacksCheckRecall

/-!
# Finite étale chart fibres over a point of an algebraic space

For an étale morphism from a scheme to an algebraic space, a point lies in the
image of `|U| → |X|` with finite fibres of both `|U| → |X|` and
`|U ×_X U| → |X|` if and only if there is a monomorphism from the spectrum of a
field in that point class whose fibre product with `U` is a finite nonempty
scheme over the field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 68.4.4. For an étale morphism from a scheme to an algebraic space,
image membership and finite fibres of both the chart and its self-pullback over
a point are equivalent to a monomorphic field-valued representative whose scheme
fibre is finite and nonempty over its field. -/
@[stacks 040U] #check (AlgebraicGeometry.AlgebraicSpace.etaleChartFiniteAbove_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S} {U : Over S}
    (φ : AlgebraicGeometry.AlgebraicSpace.ofOver U ⟶ X)
    [AlgebraicGeometry.AlgebraicSpace.Etale φ]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    (x ∈ Set.range (AlgebraicGeometry.AlgebraicSpace.Points.mapOfOver φ) ∧
      AlgebraicGeometry.AlgebraicSpace.finiteFibreOver φ x ∧
      AlgebraicGeometry.AlgebraicSpace.selfPullbackFibreFiniteOver φ x) ↔
      AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedFiniteNonemptyFibre φ x)
