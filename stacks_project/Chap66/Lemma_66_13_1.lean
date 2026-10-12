/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus

/-!
# The schematic locus of an algebraic space

Every algebraic space has a largest open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.13.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
There exists a largest open subspace of `X` which is a scheme. -/
@[stacks 03JH]
theorem exists_largest_open_scheme {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧
      ∀ (V : OpenSubspace X), IsScheme V.X →
        ∃ f : V.X ⟶ U.X, f ≫ U.ι = V.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
