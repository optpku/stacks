/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_10_6_Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Definition 71.10.6
Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`. We say
that pullbacks of meromorphic functions are defined for `f` if for every commutative
diagram with `U ∈ X_étale` and `V ∈ Y_étale` and any section `s ∈ S_Y(V)` the pullback
`f♯(s) ∈ 𝒪_X(U)` is an element of `S_X(U)`. -/
@[stacks 0EN8] #check
  (PullbacksMeromorphicFunctionsDefined :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

#check
  (regularStructureSections :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      CategoryTheory.Presheaf.SubmonoidPresheaf (commStructureSheafLift X).obj)

#check
  (pullbackStructureSection :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → {f : X ⟶ Y} →
      (sq : EtaleSquare f) →
        ((commStructureSheafLift Y).obj.obj (op sq.right) ⟶
          (commStructureSheafLift X).obj.obj (op sq.left)))

#check pullbacksMeromorphicFunctionsDefined_iff
#check pullbackStructureSection_mem
#check pullbackStructureSection_mem_ofSchemeMap
#check instPullbacksMeromorphicFunctionsDefined_id
#check EtaleSquare.ofSchemeMap
