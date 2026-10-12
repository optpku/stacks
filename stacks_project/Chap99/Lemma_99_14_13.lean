/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Noetherian.ULift
public import stacks_project.Chap98.Definition_98_13_1_Openness
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import stacks_project.Chap99.Lemma_99_14_13_Groupoids

/-!
# Lemma 99.14.13

The stack in groupoids Polarized satisfies openness of versality over `specZ`.
After the base change of Remark 99.14.5, the same axiom holds over any
Noetherian base scheme `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- `specZ` is a Noetherian scheme. -/
instance instIsNoetherian_specZ : IsNoetherian specZ :=
  inferInstance

/-- Lemma 99.14.13 (1): the stack in groupoids Polarized satisfies openness of
versality over `specZ`. -/
@[stacks 0D4V, instance]
instance instOpennessOfVersality : OpennessOfVersality toGroupoidsOverSpecZ :=
  sorry

/-- Lemma 99.14.13 (2): after base change (Remark 99.14.5), openness of
versality holds over any Noetherian base scheme `S`. -/
@[stacks 0D4V, instance]
instance instOpennessOfVersality_over {S : Scheme.{u}} [IsNoetherian S] :
    OpennessOfVersality (toGroupoidsOver S) :=
  sorry

end AlgebraicGeometry.Polarized
