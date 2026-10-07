module

public import stacks_project.Chap93.Lemma_93_12_2_Away
import StacksCheckRecall

/-!
# Flat lifts along a nilpotent pushout diagram
-/

@[expose] public section

open CategoryTheory.ModuleCat

/- Lemma 93.12.2: for a commutative diagram of Noetherian rings with cartesian
squares, flat horizontal arrows, and surjective vertical arrows whose kernels
are nilpotent, if `J' ⊆ P'` satisfies `P' ⧸ J' ≃ Q' ⧸ J' Q'` and every `M_g`
for `g ∈ J'` has an `A'`-flat `(P')_g`-lift, then an `A`-flat `P`-module `M`
has an `A'`-flat `P'`-lift if and only if `M ⊗[P] Q` has an `A'`-flat `Q'`-lift. -/
@[stacks 0DZ2]
#check @NilpotentLift.existsFlatLift_iff_existsFlatLift_extendScalars

end
