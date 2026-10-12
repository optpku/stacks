/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_29_3_InverseSystem
public import stacks_project.Chap87.Lemma_87_29_3_Over
public import stacks_project.Chap87.Lemma_87_29_3_Functor

/-!
# Lemma 87.29.3

For a McQuillan affine formal algebraic space `X = Spf(A)` over a scheme `S`,
with `A` the associated weakly admissible topological ring, the category of
finite-type inverse systems of `A ⧸ I`-algebras is anti-equivalent to the
category of finite-type morphisms of affine formal algebraic spaces over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Lemma 87.29.3: Let `S` be a scheme. Let `X` be a McQuillan affine formal
algebraic space over `S`, written `X = Spf(A)` for the associated weakly
admissible topological ring `A`. Then `spfFiniteTypeSystem hA` is an
anti-equivalence between the category `FiniteTypeInverseSystem A` of inverse
systems `(B_I)` of finite-type `A ⧸ I`-algebras with
`B_J ⧸ I B_J ≅ B_I`, and the category `AffineFiniteTypeOver (spf A hA).obj`
of finite-type morphisms `Y ⟶ Spf(A)` of affine formal algebraic spaces,
sending `(B_I)` to `Y = colim Spec(B_I)`. -/
@[stacks 0AL1]
instance instIsEquivalence_spfFiniteTypeSystem :
    (spfFiniteTypeSystem hA).IsEquivalence :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
