/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.«88_27_0_1_IsoOverOpen»
public import stacks_project.Chap88.«88_27_0_1_RigEtale»
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# The completion functor on locally finite-type morphisms isomorphic over U

Stacks 0AR5: completing along a closed subset sends locally finite-type
morphisms that are isomorphisms over the complementary open to rig-étale
morphisms of locally Noetherian formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- 88.27.0.1: the completion functor sending a morphism `f : X' ⟶ X` of
algebraic spaces that is locally of finite type and an isomorphism over the
open complement of `T` to the induced morphism `f_/T : X'_/T' ⟶ X_/T` of
formal algebraic spaces, which is rig-étale with locally Noetherian source. -/
@[stacks 0AR5]
noncomputable abbrev completionFunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X)) :=
  completionAlong.functor X T

/-- The object map of `completionFunctor X T` sends `f` to `completionAlong.map f T`. -/
theorem completionFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    (Y : completionAlong.Source X T) :
    ((completionFunctor X T).obj Y).obj.hom = completionAlong.map Y.obj.hom T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
