/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import stacks_project.Chap98.Definition_98_22_1_ObstructionTheory
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

/- Definition 98.22.1: let S be a locally Noetherian base and let X be a
category fibred in groupoids over (Sch/S)_fppf. An obstruction theory is extra
data: for every S-algebra A such that Spec(A) ⟶ S maps into an affine open and
every object x of X over Spec(A), an A-linear functor O_x : Mod_A ⥤ Mod_A of
obstruction modules; for a ring map A → B, modules M, N, and an A-linear map
M ⟶ N, an induced A-linear map O_x(M) ⟶ O_y(N) where y = x|_Spec(B); and for
every deformation situation (x, A' → A) an obstruction o_x(A') ∈ O_x(I) with
I = Ker(A' → A). These data make (x, A, M) ↦ O_x(M) a functor to sets, send
obstructions to obstructions along morphisms of deformation situations, and
satisfy Lift(x, A') nonempty iff o_x(A') = 0. -/
@[stacks 07YG]
#check ObstructionTheory

#check ObstructionTheory.spec

#check ObstructionTheory.obstruction_eq_zero_iff_nonempty_objectLift
