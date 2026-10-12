/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Basic
public import stacks_project.Chap107.Definition_107_4_1_VersalRing
public import stacks_project.Chap107.Lemma_107_2_5_Residue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Versal rings after finite residue-field extension

In Situation 107.2.1, a versal ring at a finite-type field-valued point remains
available after a finite extension of the source field, with an `S`-algebra map
that is formally smooth for the target maximal-adic topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.2.5: In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism,
where `k` is a finite type field over `S`. Let `l / k` be a finite extension of
fields and denote `x0.restrict l : Spec(l) ⟶ X` the induced morphism. Given a
versal ring `A` to `X` at `x0` there exists a versal ring `A'` to `X` at
`x0.restrict l` such that there is an `S`-algebra map `A → A'` which induces
the given field extension `l / k` and is formally smooth in the
`m_{A'}`-adic topology. -/
@[stacks 0DQY]
theorem exists_isVersalRing_restrict {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ φ : CompleteLocalSAlgebra.Hom A' A,
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
              (x0.restrict l).structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
