module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents

/-!
# Finite irreducible components on compact opens of algebraic spaces

Lemma 67.49.1 records the étale-atlas characterizations of the property that an algebraic
space has finitely many irreducible components on compact opens, including the
representable case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- Lemma 67.49.1 (1): let `S` be a scheme and let `X` be an algebraic space over `S`. The
following are equivalent: there is a surjective étale morphism `U ⟶ X` from a scheme such
that every quasi-compact open of `U` has finitely many irreducible components; for every
scheme `U` and every étale morphism `U ⟶ X` every quasi-compact open of `U` has finitely
many irreducible components; for every quasi-compact algebraic space `Y` étale over `X` the
set of codimension-`0` points of `Y` is finite; and for every quasi-compact algebraic space
`Y` étale over `X` the space `Points Y` has finitely many irreducible components. -/
@[stacks 0BB1]
theorem tfae {S : Scheme.{u}} (X : AlgebraicSpace S) :
    List.TFAE
      [existsSurjectiveEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        finiteCodimZeroOnEtaleCompact X,
        finiteIrreducibleComponentsOnEtaleCompact X] :=
  sorry

/-- Lemma 67.49.1 (2): if `X` is representable by a scheme `T` over `S`, then
`HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)` if and only if every
quasi-compact open of `T.left` has finitely many irreducible components. -/
@[stacks 0BB1]
theorem ofOver_iff {S : Scheme.{u}} (T : Over S) :
    HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T) ↔
      Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicSpace
