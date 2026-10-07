module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap69.Lemma_69_6_5_Quotient
public import stacks_project.Chap72.«72_12_5_1_Galois»

/-!
# Finite Galois base change as a free quotient of algebraic spaces

A finite Galois extension `k'/k` acts freely on the field-extension base change
of an algebraic space `X` over `k`, and the canonical projection exhibits `X`
as the free quotient of that base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldExtension

namespace Galois

/-- Lemma 72.10.3 (1): Let `k'/k` be a finite Galois extension. Let `X` be an
algebraic space over `k`. Then the opposite Galois group `(Gal(k'/k))ᵐᵒᵖ` acts
freely on the algebraic space `baseChange k k' X`. -/
@[stacks 0B86, instance]
instance instIsFree {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsFree (opAutHom k k' X) :=
  sorry

/-- Lemma 72.10.3 (2): Let `k'/k` be a finite Galois extension. Let `X` be an
algebraic space over `k`. Then `X` is the free quotient of `baseChange k k' X`
by `(Gal(k'/k))ᵐᵒᵖ` in the sense of Properties of Spaces, Lemma 66.34.1: the
canonical projection `baseChangeSnd k k' X` is a free quotient morphism for
`opAutHom k k' X`. -/
@[stacks 0B86, instance]
instance instIsFreeQuotient {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsFreeQuotient (opAutHom k k' X) (baseChangeSnd k k' X) :=
  sorry

end Galois

end AlgebraicGeometry.AlgebraicSpace.FieldExtension
