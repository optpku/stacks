/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_8_1_Modification
public import stacks_project.Chap72.Lemma_72_3_3_IsomorphismLocus

/-!
# Modifications are isomorphisms over a nonempty open

A modification of integral algebraic spaces is an isomorphism over some
nonempty open subspace of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.8.2: Let `f : X' ⟶ X` be a modification as in Definition 72.8.1.
There exists a nonempty open `U ⊂ X` such that `f⁻¹(U) ⟶ U` is an
isomorphism. -/
@[stacks 0AD9]
theorem exists_nonempty_open_isIso_of_isModification
    {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f] :
    ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
      IsIso (openInverseImageTo f U.ι) :=
  sorry

/-- The isomorphism locus of a modification of integral algebraic spaces is
nonempty. -/
theorem isomorphismLocus_nonempty_of_isModification
    {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f] :
    (isomorphismLocus f).Nonempty :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
