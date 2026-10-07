module

public import stacks_project.Chap98.Definition_98_11_1_LimitPreserving
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids

/-!
# Lemma 99.14.8

The stack in groupoids Polarized is limit preserving in the sense of
Artin's Axioms, Definition 98.11.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.8: the stack in groupoids Polarized is limit preserving
(Artin's Axioms, Definition 98.11.1). -/
@[stacks 0D43, instance]
instance instLimitPreserving :
    AlgebraicGeometry.Groupoids.LimitPreserving toGroupoidsOverSpecZ :=
  sorry

end AlgebraicGeometry.Polarized
