/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.RightKanExtension.Transitivity
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coskeletal simplicial objects

This leaf extends Mathlib's `SimplicialObject.IsCoskeletal` API with the universal mapping
equivalence from truncated objects, invariance under isomorphism, monotonicity in the truncation
level, and the corresponding unit-isomorphism criteria.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace IsCoskeletal

namespace truncation

/-- Maps into an `n`-coskeletal simplicial object are classified by maps between the
`n`-truncations. This uses only the right-Kan universal property carried by coskeletality; it does
not require a chosen coskeleton functor for all truncated objects. -/
@[stacks 018E "maps into a coskeletal object are classified by truncation"]
noncomputable def homEquiv (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    (V : SimplicialObject C) :
    (V ⟶ X) ≃ ((SimplicialObject.truncation n).obj V ⟶
      (SimplicialObject.truncation n).obj X) :=
  X.homEquivOfIsRightKanExtension
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) V

/-- The forward map of `IsCoskeletal.truncation.homEquiv` is restriction to the
`n`-truncated simplex category. -/
@[simp, stacks 018E "coskeletal truncation classifier formula"]
theorem homEquiv.apply (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    (V : SimplicialObject C) (f : V ⟶ X) :
    homEquiv X n V f = (SimplicialObject.truncation n).map f := sorry

/-- The inverse of `IsCoskeletal.truncation.homEquiv` is the universal lift supplied by the
right-Kan extension structure on the coskeletal target. -/
@[simp, stacks 018E "inverse coskeletal truncation classifier formula"]
theorem homEquiv.symm_apply (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    (V : SimplicialObject C)
    (f : (SimplicialObject.truncation n).obj V ⟶
      (SimplicialObject.truncation n).obj X) :
    (homEquiv X n V).symm f =
      X.liftOfIsRightKanExtension
        (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X)) V f := sorry

/-- Restriction to degree at most `n` is a bijection on maps into an `n`-coskeletal target. -/
@[stacks 018E "restriction into a coskeletal target is bijective"]
theorem map_bijective (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    (V : SimplicialObject C) :
    Function.Bijective (fun f : V ⟶ X ↦ (SimplicialObject.truncation n).map f) := sorry

/-- Maps into an `n`-coskeletal target are equal when their `n`-truncations are equal. -/
@[stacks 018E "coskeletal maps are determined by truncation"]
theorem hom_ext (X : SimplicialObject C) (n : ℕ) [X.IsCoskeletal n]
    {V : SimplicialObject C} {f g : V ⟶ X}
    (h : (SimplicialObject.truncation n).map f =
      (SimplicialObject.truncation n).map g) :
    f = g := sorry

end truncation

/-- Coskeletality is invariant under isomorphism. -/
@[stacks 018B "coskeletality is invariant under isomorphism"]
theorem ofIso {X Y : SimplicialObject C} {n : ℕ}
    [X.IsCoskeletal n] (e : X ≅ Y) : Y.IsCoskeletal n := sorry

/-- Explicit-proof bridge for invariance of coskeletality under isomorphism. -/
@[stacks 018B "explicit coskeletality invariance bridge"]
theorem ofIso.explicit {X Y : SimplicialObject C} {n : ℕ}
    (hX : X.IsCoskeletal n) (e : X ≅ Y) : Y.IsCoskeletal n := sorry

/-- An `n`-coskeletal simplicial object is `m`-coskeletal for every
`n ≤ m`. -/
@[stacks 018B "coskeletality is monotone"]
theorem ofLE {X : SimplicialObject C} {n m : ℕ}
    [X.IsCoskeletal n] (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)] :
    X.IsCoskeletal m := sorry

/-- Explicit-proof bridge for monotonicity of coskeletality. -/
@[stacks 018B "explicit coskeletality monotonicity bridge"]
theorem ofLE.explicit {X : SimplicialObject C} {n m : ℕ}
    (hX : X.IsCoskeletal n) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)] :
    X.IsCoskeletal m := sorry

/-- The unit at an `n`-coskeletal object is an isomorphism at every higher coskeleton level. -/
@[stacks 018B "coskeleton unit is invertible above a coskeletal level"]
theorem unit.isIso_of_le {X : SimplicialObject C} {n m : ℕ}
    [X.IsCoskeletal n] (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)]
    [SimplicialObject.Truncated.HasCoskeletons C m] :
    IsIso ((coskAdj m).unit.app X) := sorry

/-- Explicit-proof bridge for invertibility of higher coskeleton units. -/
@[stacks 018B "explicit coskeleton-unit invertibility bridge"]
theorem unit.isIso_of_le.explicit {X : SimplicialObject C} {n m : ℕ}
    (hX : X.IsCoskeletal n) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)]
    [SimplicialObject.Truncated.HasCoskeletons C m] :
    IsIso ((coskAdj m).unit.app X) := sorry

end IsCoskeletal

namespace coskAdj

namespace unit

/-- If the unit of the `n`-coskeleton adjunction is invertible, then so is the unit at every
higher level. -/
@[stacks 018B "coskeleton unit isomorphisms are monotone"]
theorem isIso_of_le {X : SimplicialObject C} {n m : ℕ}
    (h : n ≤ m)
    [SimplicialObject.Truncated.HasCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)]
    [IsIso ((coskAdj n).unit.app X)] :
    IsIso ((coskAdj m).unit.app X) := sorry

/-- Explicit-proof bridge for monotonicity of coskeleton-unit invertibility. -/
@[stacks 018B "explicit coskeleton-unit monotonicity bridge"]
theorem isIso_of_le.explicit {X : SimplicialObject C} {n m : ℕ}
    (h : n ≤ m)
    [SimplicialObject.Truncated.HasCoskeletons C n]
    [SimplicialObject.Truncated.HasCoskeletons C m]
    [SimplicialObject.Truncated.HasPointwiseCoskeleton
      ((SimplicialObject.truncation n).obj X)]
    (hn : IsIso ((coskAdj n).unit.app X)) :
    IsIso ((coskAdj m).unit.app X) := sorry

end unit

end coskAdj

namespace Truncated

variable {n : ℕ}
variable [SimplicialObject.Truncated.HasPointwiseCoskeletons C n]

namespace cosk

/-- The canonical `n`-coskeleton is `n`-coskeletal. -/
@[stacks 018B "a coskeleton is coskeletal"]
instance isCoskeletal (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n).obj U).IsCoskeletal n := sorry

/-- An `n`-coskeleton is coskeletal at every level at least `n`. -/
@[stacks 018B "coskeletality of a chosen coskeleton is monotone"]
theorem isCoskeletal_of_le {m : ℕ} (U : SimplicialObject.Truncated C n) (h : n ≤ m) :
    ((Truncated.cosk n).obj U).IsCoskeletal m := sorry

/-- The higher coskeleton unit at an `n`-coskeleton is an isomorphism. -/
@[stacks 018B "higher coskeleton unit of a chosen coskeleton"]
theorem unit.isIso_of_le {m : ℕ}
    [SimplicialObject.Truncated.HasCoskeletons C m]
    (U : SimplicialObject.Truncated C n) (h : n ≤ m) :
    IsIso ((coskAdj m).unit.app ((Truncated.cosk n).obj U)) := sorry

end cosk

namespace coskeleton

/-- A chosen pointwise coskeleton of a truncated simplicial object is coskeletal at its defining
truncation level.  This objectwise owner is available without choosing coskeleta for the whole
coefficient category. -/
@[stacks 018B "a chosen pointwise coskeleton is coskeletal"]
instance isCoskeletal {n : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] : U.coskeleton.IsCoskeletal n := sorry

/-- A chosen pointwise coskeleton is coskeletal at every truncation level at least its defining
level. -/
@[stacks 018B "chosen coskeletality is monotone"]
theorem isCoskeletal_of_le {n m : ℕ} (U : SimplicialObject.Truncated C n)
    [U.HasPointwiseCoskeleton] (h : n ≤ m) :
    U.coskeleton.IsCoskeletal m := sorry

end coskeleton

end Truncated

end CategoryTheory.SimplicialObject
