module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap68.Lemma_68_4_5_Fibre

/-!
# Finite fibres above a point of an algebraic space

Six pointwise tests at a point of an algebraic space are equivalent: affine
étale charts with finite `|U|` and `|U ×_X U|` fibres, an étale scheme covering
with those finite fibres, a field-valued monomorphism with finite affine étale
fibres over the field, and the quasi-compact field-valued-point formulations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. The following are equivalent:
`forallAffineEtaleFiniteAbove X x`, `existsEtaleCoverFiniteAbove X x`,
`existsMonoFieldValuedFiniteAffineFibres X x`,
`existsQuasiCompactMonoFieldValuedPoint X x`,
`existsQuasiCompactFieldValuedPoint X x`, and
`forallFieldValuedPointQuasiCompact X x`. -/
@[stacks 03JV]
theorem finiteAbove_tfae {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    List.TFAE
      [ forallAffineEtaleFiniteAbove X x
      , existsEtaleCoverFiniteAbove X x
      , existsMonoFieldValuedFiniteAffineFibres X x
      , existsQuasiCompactMonoFieldValuedPoint X x
      , existsQuasiCompactFieldValuedPoint X x
      , forallFieldValuedPointQuasiCompact X x ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
