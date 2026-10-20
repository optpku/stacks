/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Exactness detected by a conservative family of points

This module isolates the pointwise criterion saying that a continuous functor
has exact sheaf pullback when every composite with a point in a conservative
family is realized by a source point.
-/

@[expose] public section

open CategoryTheory Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- `u` has a pointwise fiber realization from `(C, J)` along `P` when composing `u` with the
fiber functor of every point in `P` is naturally isomorphic to the fiber functor of a point of
the source site. -/
def HasPointwiseFiberRealization (u : C ⥤ D)
    (J : GrothendieckTopology C) (P : ObjectProperty (Point.{w} K)) : Prop :=
  ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Nonempty (Ψ.fiber ≅ u ⋙ Φ.obj.fiber)

/-- The strict-equality presentation of `HasPointwiseFiberRealization`.  This is useful when a
chosen point fiber is definitionally identified with a composite; the isomorphism-valued
predicate is the invariant public interface. -/
def HasPointwiseFiberRealizationEq (u : C ⥤ D)
    (J : GrothendieckTopology C) (P : ObjectProperty (Point.{w} K)) : Prop :=
  ∀ Φ : P.FullSubcategory, ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber

namespace HasPointwiseFiberRealization

variable {u : C ⥤ D} {P : ObjectProperty (Point.{w} K)}

/-- Extract the source point and fiber isomorphism realizing the composite fiber functor at one
member of `P`. -/
theorem exists_point (hu : u.HasPointwiseFiberRealization J P) (Φ : P.FullSubcategory) :
    ∃ Ψ : Point.{w} J, Nonempty (Ψ.fiber ≅ u ⋙ Φ.obj.fiber) := sorry

end HasPointwiseFiberRealization

namespace HasPointwiseFiberRealizationEq

variable {u : C ⥤ D} {P : ObjectProperty (Point.{w} K)}

/-- A strict pointwise fiber realization supplies the invariant isomorphism-valued realization. -/
theorem toIsomorphic (hu : u.HasPointwiseFiberRealizationEq J P) :
    u.HasPointwiseFiberRealization J P := sorry

/-- Extract the source point whose fiber is strictly equal to the selected composite fiber. -/
theorem exists_point (hu : u.HasPointwiseFiberRealizationEq J P) (Φ : P.FullSubcategory) :
    ∃ Ψ : Point.{w} J, Ψ.fiber = u ⋙ Φ.obj.fiber := sorry

end HasPointwiseFiberRealizationEq

namespace HasPointwiseFiberRealization

variable {u : C ⥤ D} {P : ObjectProperty (Point.{w} K)}

/-- A continuous functor has exact pullback on set-valued sheaves when `hu` realizes its
composites with a conservative family of target points by source points. -/
theorem exactSheafPullback
    (hu : u.HasPointwiseFiberRealization J P) [u.IsContinuous J K]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (hP : P.IsConservativeFamilyOfPoints) :
    exactFunctor (Sheaf J (Type w)) (Sheaf K (Type w)) (u.sheafPullback (Type w) J K) := sorry

/-- Under `hu`, sheaf pullback preserves finite limits. -/
theorem preservesFiniteLimits
    (hu : u.HasPointwiseFiberRealization J P) [u.IsContinuous J K]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (hP : P.IsConservativeFamilyOfPoints) :
    PreservesFiniteLimits (u.sheafPullback (Type w) J K) := sorry

/-- `hu` presents sheaf pullback as the inverse image of a morphism of topoi.  The local
`PreservesFiniteLimits` instance is proof data determined by the explicit realization hypotheses
and is intentionally confined to this construction. -/
noncomputable def morphismOfTopoiIn
    (hu : u.HasPointwiseFiberRealization J P) [u.IsContinuous J K]
    [LocallySmall.{w} C] [LocallySmall.{w} D]
    [HasWeakSheafify K (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension F]
    (hP : P.IsConservativeFamilyOfPoints) :
    MorphismOfTopoiIn J K :=
  letI : PreservesFiniteLimits (u.sheafPullback (Type w) J K) :=
    hu.preservesFiniteLimits hP
  u.morphismOfTopoiInOfContinuous J K

end HasPointwiseFiberRealization

end CategoryTheory.Functor
