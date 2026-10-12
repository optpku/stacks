/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Remark_85_4_1_Fiberwise
public import stacks_project.Chap85.Remark_85_4_1_MorphismDiagram
import StacksCheckRecall

/-!
# Remark 85.4.1

In Situation 85.3.3, an augmentation `a0` towards a site `D` is either a
morphism of sites `C.obj ⦋0⦌ ⟶ D` presented by a continuous functor `u0`, or a
morphism of topoi `Sh(C0) ⟶ Sh(D)` presented by a cocontinuous functor `u0`,
with composites along all `φ : ⦋0⦌ ⟶ n` independent of `φ`.
-/

@[expose] public section

open CategoryTheory

/- Remark 85.4.1 (1): case A, a morphism of sites `a0 : C.obj ⦋0⦌ ⟶ D` given by
a continuous functor `u0 : D ⥤ C.obj ⦋0⦌` such that `u_φ ∘ u0` is independent of
`φ : ⦋0⦌ ⟶ n`. -/
@[stacks 0D6Z] #check @SimplicialSites.IsAugmentation
@[stacks 0D6Z] #check @SimplicialSites.IsAugmentation.toposMap
@[stacks 0D6Z] #check @SimplicialSites.IsAugmentation.stageFunctor

/- Remark 85.4.1 (2): case B, a morphism of topoi `a0 : Sh(C0) ⟶ Sh(D)` given by
a cocontinuous functor `u0 : C0 ⥤ D` such that `u0 ∘ u_φ` is independent of
`φ : ⦋0⦌ ⟶ n`. -/
@[stacks 0D6Z] #check @Grothendieck.IsAugmentation
@[stacks 0D6Z] #check @Grothendieck.IsAugmentation.toposMap
@[stacks 0D6Z] #check @Grothendieck.IsAugmentation.stageFunctor
