module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.49.1: The four étale-atlas characterizations of finiteness of irreducible
components on quasi-compact opens of an algebraic space are equivalent. -/
@[stacks 0BB1]
#check (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens.tfae :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    List.TFAE
      [AlgebraicSpace.existsSurjectiveEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        AlgebraicSpace.forallEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        AlgebraicSpace.finiteCodimZeroOnEtaleCompact X,
        AlgebraicSpace.finiteIrreducibleComponentsOnEtaleCompact X])

/- For a representable algebraic space, the property is exactly finiteness of irreducible
components on every quasi-compact open of the representing scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens.ofOver_iff :
  ∀ {S : Scheme.{u}} (T : Over S),
    AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens (AlgebraicSpace.ofOver T) ↔
      Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left)
