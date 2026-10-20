/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.CategoryTheory.Sites.Family.Overlap.Basic
import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Colimits local for fpqc coverings

This module records a criterion for a cocone of schemes to be colimiting when that property holds
after pullback to every member and every pairwise overlap of an fpqc covering family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w z

namespace AlgebraicGeometry.Scheme.FpqcCovering

/-- A cocone of schemes is colimiting if its pullbacks to every member and every pairwise overlap
of an fpqc covering family are colimiting. -/
theorem isColimit_of_fpqcCover {J : Type v} [Category.{w} J]
    {X : J ⥤ Scheme.{u}} (t : Cocone X)
    (𝒰 : SemiRepresentableFamily.Over.{z} t.pt) (h𝒰 : Scheme.FpqcCovering 𝒰.obj)
    (memberDiagram : ∀ a : 𝒰.index, J ⥤ Scheme.{u})
    (memberMap : ∀ a : 𝒰.index, memberDiagram a ⟶ X)
    (memberLeg : ∀ a : 𝒰.index,
      memberDiagram a ⟶ (Functor.const J).obj (𝒰.obj a).left)
    (memberPullback : ∀ (a : 𝒰.index) (i : J),
      IsPullback ((memberLeg a).app i) ((memberMap a).app i)
        (𝒰.obj a).hom (t.ι.app i))
    (memberColimit : ∀ a : 𝒰.index,
      Nonempty (IsColimit (Cocone.mk (𝒰.obj a).left (memberLeg a))))
    (overlapDiagram : ∀ a b : 𝒰.index, J ⥤ Scheme.{u})
    (overlapMap : ∀ a b : 𝒰.index, overlapDiagram a b ⟶ X)
    (overlapLeg : ∀ a b : 𝒰.index,
      overlapDiagram a b ⟶ (Functor.const J).obj (𝒰.Overlap a b))
    (overlapPullback : ∀ (a b : 𝒰.index) (i : J),
      IsPullback ((overlapLeg a b).app i) ((overlapMap a b).app i)
        (𝒰.overlapMap a b) (t.ι.app i))
    (overlapColimit : ∀ a b : 𝒰.index,
      Nonempty (IsColimit (Cocone.mk (𝒰.Overlap a b) (overlapLeg a b)))) :
    Nonempty (IsColimit t) := sorry

end AlgebraicGeometry.Scheme.FpqcCovering
