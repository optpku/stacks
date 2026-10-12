/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_22_1_DMLocus

/-!
# Largest open DM and quasi-DM substacks

An algebraic stack has a largest open DM substack and a largest open quasi-DM
substack, nested as open substacks of the ambient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.22.1 (1): Let `X` be an algebraic stack. There is a largest open
DM substack of `X`. -/
@[stacks 0DSM]
theorem dmLocus_isLargest {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : OpenSubstack X) (hV : IsDM V.Y) :
    V.pointsSet ⊆ (dmLocus X).pointsSet :=
  sorry

/-- Lemma 101.22.1 (2): Let `X` be an algebraic stack. There is a largest open
quasi-DM substack of `X`. -/
@[stacks 0DSM]
theorem quasiDMLocus_isLargest {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : OpenSubstack X) (hV : IsQuasiDM V.Y) :
    V.pointsSet ⊆ (quasiDMLocus X).pointsSet :=
  sorry

/-- Lemma 101.22.1 (3): Let `X` be an algebraic stack. The largest open DM
substack of `X` is contained in the largest open quasi-DM substack. -/
@[stacks 0DSM]
theorem dmLocus_subset_quasiDMLocus {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (dmLocus X).pointsSet ⊆ (quasiDMLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicStack
