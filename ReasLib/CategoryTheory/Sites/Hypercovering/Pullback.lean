/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Sites.Hypercovering.FixedTarget
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of hypercoverings

This leaf owns the topology-relative pullback construction for formal-coproduct
hypercoverings.  It separates the degreewise matching-object comparison map
from the covering hypotheses used to assemble the resulting hypercovering.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite
open Limits
open SemiRepresentableFamily.OverFamily
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Hypercovering

variable [HasPullbacks C]
variable {X : C}

/-- The two maps from the degree `n + 1` term of `M` to the matching object of `L` agree:
one is induced by `b`, and the other is the matching map of `M` followed by the coskeleton map.
This is the compatibility required to form the pullback comparison map. -/
theorem matchingPullbackMap_condition
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ) :
    b.app (op <| SimplexCategory.mk (n + 1)) ≫ SimplicialObject.matchingMap L n =
      SimplicialObject.matchingMap M n ≫
        ((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1)) := sorry

/-- The canonical degreewise map from `M` to the pullback of the matching maps of a simplicial
morphism `b : M ⟶ L`. -/
noncomputable def matchingPullbackMap
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ) :
    M.obj (op <| SimplexCategory.mk (n + 1)) ⟶
      pullback (SimplicialObject.matchingMap L n)
        (((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1))) :=
  pullback.lift
    (b.app (op <| SimplexCategory.mk (n + 1)))
    (SimplicialObject.matchingMap M n)
    (matchingPullbackMap_condition b n)

/-- The first projection of `matchingPullbackMap` is the degree `n + 1` component of `b`. -/
@[reassoc]
theorem matchingPullbackMap_fst
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ) :
    matchingPullbackMap b n ≫
      pullback.fst (SimplicialObject.matchingMap L n)
        (((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1))) =
      b.app (op <| SimplexCategory.mk (n + 1)) := sorry

/-- The second projection of `matchingPullbackMap` is the matching map of `M`. -/
@[reassoc]
theorem matchingPullbackMap_snd
    {L M : SimplicialObject (SR(C, X))}
    (b : M ⟶ L) (n : ℕ) :
    matchingPullbackMap b n ≫
      pullback.snd (SimplicialObject.matchingMap L n)
        (((SimplicialObject.cosk n).map b).app (op <| SimplexCategory.mk (n + 1))) =
      SimplicialObject.matchingMap M n := sorry

/-- The degree-zero family of the simplicial pullback is covering when the degree-zero component
of the right-hand simplicial map is covering. -/
theorem pullback_zero_isCovering
    (K : Hypercovering J X)
    {L M : SimplicialObject (SR(C, X))}
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : SemiRepresentableFamily.OverFamily.covering J
      (b.app (op <| SimplexCategory.mk 0))) :
    ((pullback a b).obj (op <| SimplexCategory.mk 0)).toSieve ∈ J X := sorry

/-- The higher matching maps of the simplicial pullback are covering when the corresponding
matching-pullback maps of the right-hand simplicial map are covering. -/
theorem pullback_succ_isCovering
    (K : Hypercovering J X)
    {L M : SimplicialObject (SR(C, X))}
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hmatching : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J (matchingPullbackMap b n))
    (n : ℕ) :
    SemiRepresentableFamily.OverFamily.covering J
      (SimplicialObject.matchingMap (pullback a b) n) := sorry

/-- The pullback of a hypercovering along a simplicial map satisfying the degree-zero and
matching-covering hypotheses. -/
@[stacks 01GH "pullback of a hypercovering"]
noncomputable def pullback
    (K : Hypercovering J X)
    (L M : SimplicialObject (SR(C, X)))
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : SemiRepresentableFamily.OverFamily.covering J
      (b.app (op <| SimplexCategory.mk 0)))
    (hmatching : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J (matchingPullbackMap b n)) :
    Hypercovering J X where
  toSimplicialObject := Limits.pullback a b
  zero_isCovering := pullback_zero_isCovering K a b hb0
  succ_isCovering := pullback_succ_isCovering K a b hmatching

/-- The underlying simplicial object of `Hypercovering.pullback` is the categorical pullback of
the two input simplicial maps. -/
@[simp]
theorem pullback_toSimplicialObject
    (K : Hypercovering J X)
    (L M : SimplicialObject (SR(C, X)))
    (a : K.toSimplicialObject ⟶ L) (b : M ⟶ L)
    (hb0 : SemiRepresentableFamily.OverFamily.covering J
      (b.app (op <| SimplexCategory.mk 0)))
    (hmatching : ∀ n : ℕ,
      SemiRepresentableFamily.OverFamily.covering J (matchingPullbackMap b n)) :
    (pullback K L M a b hb0 hmatching).toSimplicialObject = Limits.pullback a b := sorry

end Hypercovering

end CategoryTheory
