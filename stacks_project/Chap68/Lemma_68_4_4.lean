module

public import stacks_project.Chap68.Lemma_68_4_4_Fibre

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. Let `U` be a scheme and let `φ : ofOver U ⟶ X` be an
étale morphism. The following are equivalent: `x` is in the image of `|U| → |X|`,
and setting `R = U ×_X U` the fibres of both `|U| → |X|` and `|R| → |X|` over `x`
are finite; and there exists a monomorphism `Spec(k) ⟶ X` with `k` a field in the
equivalence class of `x` such that `Spec(k) ×_X U` is a finite nonempty scheme
over `k`. -/
@[stacks 040U]
theorem etaleChartFiniteAbove_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] (x : Points X) :
    (x ∈ Set.range (Points.mapOfOver φ) ∧ finiteFibreOver φ x ∧
      selfPullbackFibreFiniteOver φ x) ↔
      existsMonoFieldValuedFiniteNonemptyFibre φ x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
