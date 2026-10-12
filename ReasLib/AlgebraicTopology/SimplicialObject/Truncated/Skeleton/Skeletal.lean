/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeletal
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Between.Restriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen skeleta and skeletal simplicial objects

This file connects the intrinsic predicate `SimplicialObject.IsSkeletal` to a chosen objectwise
skeleton.  The primary comparison requires a skeleton only for the single truncated object under
consideration; APIs involving `skAdj` are compatibility bridges for ambient categories carrying
all skeleta.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace Truncated.skeleton

/-- The canonical comparison from a chosen skeleton of the truncation of `X` to `X`. -/
noncomputable def counit (X : SimplicialObject C) (n : ℕ)
    [((SimplicialObject.truncation n).obj X).HasSkeleton] :
    ((SimplicialObject.truncation n).obj X).skeleton ⟶ X :=
  desc ((SimplicialObject.truncation n).obj X) X (𝟙 _)

/-- Restricting the chosen-skeleton comparison recovers the identity of the truncation. -/
@[reassoc (attr := simp)]
theorem unit_counit (X : SimplicialObject C) (n : ℕ)
    [((SimplicialObject.truncation n).obj X).HasSkeleton] :
    unit ((SimplicialObject.truncation n).obj X) ≫
        (SimplexCategory.Truncated.inclusion n).op.whiskerLeft (counit X n) =
      𝟙 _ := sorry

/-- A simplicial object is skeletal exactly when its chosen single-object skeleton comparison is
invertible. -/
theorem isSkeletal_iff_isIso (X : SimplicialObject C) (n : ℕ)
    [((SimplicialObject.truncation n).obj X).HasSkeleton] :
    X.IsSkeletal n ↔ IsIso (counit X n) := sorry

namespace counit

/-- The chosen-skeleton comparison of a skeletal object is invertible. -/
instance isIso (X : SimplicialObject C) (n : ℕ)
    [((SimplicialObject.truncation n).obj X).HasSkeleton]
    [X.IsSkeletal n] : IsIso (Truncated.skeleton.counit X n) := sorry

end counit

end Truncated.skeleton

namespace IsSkeletal

/-- An `n`-skeletal object is `m`-skeletal for `n ≤ m`, assuming the exact pointwise skeleton
needed for the intermediate truncation. -/
theorem ofLE {X : SimplicialObject C} {n m : ℕ}
    [X.IsSkeletal n] (h : n ≤ m)
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)] :
    X.IsSkeletal m := sorry

/-- Explicit-proof form of monotonicity of skeletality. -/
theorem ofLE.explicit {X : SimplicialObject C} {n m : ℕ}
    (hX : X.IsSkeletal n) (h : n ≤ m)
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)] :
    X.IsSkeletal m := sorry

namespace counit

/-- The chosen skeleton comparison at every higher level is invertible. -/
theorem isIso_of_le {X : SimplicialObject C} {n m : ℕ}
    [X.IsSkeletal n] (h : n ≤ m)
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)]
    [Truncated.HasSkeleton ((SimplicialObject.truncation m).obj X)] :
    IsIso (Truncated.skeleton.counit X m) := sorry

/-- Explicit-proof form of invertibility of higher chosen-skeleton comparisons. -/
theorem isIso_of_le.explicit {X : SimplicialObject C} {n m : ℕ}
    (hX : X.IsSkeletal n) (h : n ≤ m)
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)]
    [Truncated.HasSkeleton ((SimplicialObject.truncation m).obj X)] :
    IsIso (Truncated.skeleton.counit X m) := sorry

end counit

end IsSkeletal

namespace Truncated.skeleton

/-- A pointwise chosen skeleton is skeletal at its defining truncation level. -/
@[stacks 018N "a chosen pointwise skeleton is skeletal"]
instance isSkeletal {n : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseSkeleton] : U.skeleton.IsSkeletal n := sorry

/-- A pointwise chosen `n`-skeleton is skeletal at every level at least `n`. -/
@[stacks 018N "skeletality of a chosen skeleton is monotone"]
theorem isSkeletal_of_le {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseSkeleton] (h : n ≤ m) :
    U.skeleton.IsSkeletal m := sorry

end Truncated.skeleton

namespace Truncated.sk

variable {n : ℕ}

/-- The canonical `n`-skeleton is `n`-skeletal. -/
@[stacks 018N "a canonical skeleton is skeletal"]
instance isSkeletal (U : SimplicialObject.Truncated C n)
    [Truncated.HasSkeletons C n] :
    ((Truncated.sk n).obj U).IsSkeletal n := sorry

/-- A canonical `n`-skeleton is skeletal at every level at least `n`. -/
theorem isSkeletal_of_le {m : ℕ} (U : SimplicialObject.Truncated C n) (h : n ≤ m)
    [Truncated.HasPointwiseSkeletons C n] :
    ((Truncated.sk n).obj U).IsSkeletal m := sorry

/-- The higher skeleton counit at a canonical `n`-skeleton is an isomorphism. -/
theorem counit.isIso_of_le {m : ℕ}
    [Truncated.HasPointwiseSkeletons C n] [Truncated.HasSkeletons C m]
    (U : SimplicialObject.Truncated C n) (h : n ≤ m) :
    IsIso ((skAdj m).counit.app ((Truncated.sk n).obj U)) := sorry

end Truncated.sk

/-- Under ambient chosen skeleta, the single-object comparison agrees with the counit of
`skAdj`. -/
theorem Truncated.skeleton.counit_eq_skAdj (X : SimplicialObject C) (n : ℕ)
    [Truncated.HasSkeletons C n] :
    Truncated.skeleton.counit X n = (skAdj n).counit.app X := sorry

/-- With ambient chosen skeleta, skeletality is equivalent to invertibility of the skeleton
adjunction counit. -/
theorem isSkeletal_iff_isIso (X : SimplicialObject C) (n : ℕ)
    [Truncated.HasSkeletons C n] :
    X.IsSkeletal n ↔ IsIso ((skAdj n).counit.app X) := sorry

namespace skAdj.counit

/-- The skeleton-adjunction counit of a skeletal object is invertible. -/
instance isIso_of_isSkeletal (X : SimplicialObject C) (n : ℕ)
    [Truncated.HasSkeletons C n] [X.IsSkeletal n] :
    IsIso ((skAdj n).counit.app X) := sorry

/-- Invertibility of skeleton-adjunction counits is monotone in the truncation level. -/
theorem isIso_of_le {X : SimplicialObject C} {n m : ℕ} (h : n ≤ m)
    [Truncated.HasSkeletons C n] [Truncated.HasSkeletons C m]
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)]
    [IsIso ((skAdj n).counit.app X)] :
    IsIso ((skAdj m).counit.app X) := sorry

/-- Explicit-proof form of monotonicity of skeleton-adjunction counits. -/
theorem isIso_of_le.explicit {X : SimplicialObject C} {n m : ℕ} (h : n ≤ m)
    [Truncated.HasSkeletons C n] [Truncated.HasSkeletons C m]
    [Truncated.HasPointwiseSkeleton ((SimplicialObject.truncation n).obj X)]
    (hn : IsIso ((skAdj n).counit.app X)) :
    IsIso ((skAdj m).counit.app X) := sorry

end skAdj.counit

end CategoryTheory.SimplicialObject
