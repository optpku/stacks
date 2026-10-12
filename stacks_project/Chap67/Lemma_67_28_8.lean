/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

/-!
# Finite presentation over a quasi-compact quasi-separated algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.28.8: Let `S` be a scheme. Let `Y` be an algebraic space over `S`
which is quasi-compact and quasi-separated. If `X` is of finite presentation
over `Y`, then `X` is quasi-compact and quasi-separated. -/
@[stacks 06G5]
theorem isQuasiCompact_and_isQuasiSeparated_of_finitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] [FinitePresentation f] :
    IsQuasiCompact X ∧ IsAbsolutelyQuasiSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
