/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_19_2_AutomorphismGroup
public import stacks_project.Chap101.Lemma_101_22_2_DMLocus

/-!
# Points of the DM and quasi-DM loci

A field-valued point of an algebraic stack lies in the DM locus exactly when
its automorphism group algebraic space is unramified over the ground field, and
in the quasi-DM locus exactly when that group space is locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.22.2 (1): Let `X` be an algebraic stack. Let `x ∈ |X|` correspond
to a field-valued point `p : Spec(k) ⟶ X`. Let `G_x` be the automorphism group
algebraic space of `p`. Then `x` is in the DM locus of `X` if and only if
`G_x ⟶ Spec(k)` is unramified. -/
@[stacks 0DSN]
theorem memDMLocus_iff_unramified {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    memDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.Unramified S) p :=
  sorry

/-- Lemma 101.22.2 (2): Let `X` be an algebraic stack. Let `x ∈ |X|` correspond
to a field-valued point `p : Spec(k) ⟶ X`. Let `G_x` be the automorphism group
algebraic space of `p`. Then `x` is in the quasi-DM locus of `X` if and only if
`G_x ⟶ Spec(k)` is locally quasi-finite. -/
@[stacks 0DSN]
theorem memQuasiDMLocus_iff_locallyQuasiFinite {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (p : FieldValuedPoint X) :
    memQuasiDMLocus (Points.mk p) ↔
      automorphismGroup.Has (@AlgebraicSpace.LocallyQuasiFinite S) p :=
  sorry

end AlgebraicGeometry.AlgebraicStack
