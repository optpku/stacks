/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced structures on image closures

This module packages the reduced induced structure on the closure of the range of a morphism,
and compares it with the scheme-theoretic image when the source is reduced.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The reduced induced scheme on the closure of the range of a morphism over a base scheme,
equipped with its structure morphism to that base. -/
noncomputable def reducedImageClosureOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) : Over S :=
  Over.mk
    ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.left))).subschemeι ≫ Y.hom)

/-- The canonical inclusion of the reduced image closure into the target, as a morphism over
the base scheme. -/
noncomputable def reducedImageClosureιOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) : reducedImageClosureOver f ⟶ Y :=
  Over.homMk
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.left))).subschemeι (by rfl)

/-- The range of the reduced image-closure inclusion is the closure of the range of the original
morphism. -/
theorem range_reducedImageClosureιOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Set.range (reducedImageClosureιOver f).left =
      TopologicalSpace.Closeds.closure (Set.range f.left) := sorry

/-- A source point regarded as a point of the reduced closure of the morphism's image. -/
noncomputable def asReducedImageClosureOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (x : X.left) :
    (reducedImageClosureOver f).left :=
  ⟨f.left x, subset_closure ⟨x, rfl⟩⟩

/-- The reduced image-closure inclusion sends the canonical point associated to `x` to
`f.left x`. -/
theorem reducedImageClosureιOver_apply_asReducedImageClosureOver
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (x : X.left) :
    (reducedImageClosureιOver f).left (asReducedImageClosureOver f x) = f.left x := sorry

/-- For a morphism from a reduced scheme, its kernel ideal sheaf is the vanishing ideal of the
closure of its range. -/
@[stacks 056B "kernel ideal of the reduced scheme-theoretic image"]
theorem ker_eq_vanishingIdeal_closure_range_of_isReduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f)) := by
  apply le_antisymm
  · rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    exact f.range_subset_ker_support
  · rw [Scheme.IdealSheafData.le_ker_iff_range_subset,
      Scheme.IdealSheafData.support_vanishingIdeal]
    exact subset_closure

/-- The scheme-theoretic image of a morphism from a reduced scheme is the reduced induced scheme
structure on the closure of its range. -/
@[stacks 056B]
theorem image_eq_vanishingIdeal_subscheme_closure_range_of_isReduced
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.image = (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f))).subscheme := by
  change f.ker.subscheme = _
  rw [ker_eq_vanishingIdeal_closure_range_of_isReduced]

end AlgebraicGeometry.Scheme.Hom
