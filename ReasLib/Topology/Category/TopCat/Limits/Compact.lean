/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compact Limits in `TopCat`

Compactness of limiting cones over compact Hausdorff spaces is independent of
cofilteredness. This leaf keeps that general result separate from descent
statements for cofiltered diagrams.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v w

namespace TopCat

variable {X Y Z : TopCat.{u}}

/-- A pullback of locally compact spaces over a Hausdorff space is locally compact. -/
instance locallyCompactSpace_pullback [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [T2Space Z] (f : X ⟶ Z) (g : Y ⟶ Z) :
    LocallyCompactSpace (pullback f g : TopCat) := sorry

/-- A pullback of compact spaces over a Hausdorff space is compact. -/
@[stacks 09WZ "compact pullbacks over Hausdorff spaces"]
instance compactSpace_pullback [CompactSpace X] [CompactSpace Y] [T2Space Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) : CompactSpace (pullback f g : TopCat) := sorry

namespace IsLimit

variable {J : Type v} [Category.{w} J]
variable {F : J ⥤ TopCat.{max v u}} {C : Cone F}

/-- A limiting cone over compact Hausdorff spaces has a compact cone point. This is stated for an
arbitrary chosen limit cone so downstream arguments do not need to transport through
`limit.isoLimitCone`. -/
@[stacks 08ZV "compactness of an arbitrary compact Hausdorff limit cone"]
theorem compactSpace_of_compactSpace_t2Space (hC : IsLimit C)
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    CompactSpace C.pt := sorry

end IsLimit

variable {J : Type v} [Category.{w} J]
variable (F : J ⥤ TopCat.{max u v})

/-- Lemma 5.14.5: the limit of a diagram of compact Hausdorff topological
spaces is compact. -/
@[stacks 08ZV]
theorem compactSpace_limit_of_compactSpace_t2Space
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    CompactSpace (limit F : TopCat) := sorry

end TopCat
