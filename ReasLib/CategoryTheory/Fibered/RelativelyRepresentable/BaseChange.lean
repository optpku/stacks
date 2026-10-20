/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.HomProperty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relatively representable morphisms of categories fibred in groupoids

The ordinary fixed-universe base-change construction, its relative-representability predicate,
and the corresponding bicategorical hom-property closure API.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- A morphism `F : X ⟶ Y` in the fixed bicategory of categories fibred in groupoids is
relatively representable when every bicategorical base change along a morphism from a slice
fibration is representable.

The `MorphismProperty` presentation keeps the endpoints implicit, so it is the ergonomic
predicate used in theorem statements. The pair-indexed bicategorical owner, including its
closure API, is `relativelyRepresentable.homProperty` below. -/
@[stacks 02Y7 "relative representability of a morphism of groupoid fibrations"]
def relativelyRepresentable :
    MorphismProperty (Groupoids C) :=
  fun _ Y F ↦
    ∀ ⦃U : C⦄ (G : slice U ⟶ Y),
      IsRepresentable (baseChange F G)

/-- Relative representability as a property of `1`-morphisms in the bicategory of categories
fibred in groupoids.

Unlike the implicit-endpoint `relativelyRepresentable` predicate, this is indexed by both source
and target and therefore plugs directly into the neutral `Bicategory.HomProperty`
infrastructure for identities, horizontal composition, and locally induced bicategories. -/
@[stacks 02Y7 "bicategorical hom-property of relatively representable morphisms"]
def relativelyRepresentable.homProperty :
    Bicategory.HomProperty (fun X : Groupoids C ↦ X) :=
  fun _ _ F ↦ relativelyRepresentable F

/-- The bicategorical hom-property owner computes to the convenient implicit-endpoint predicate. -/
@[simp]
theorem relativelyRepresentable.homProperty_apply
    {X Y : Groupoids C} (F : X ⟶ Y) :
    relativelyRepresentable.homProperty X Y F ↔ relativelyRepresentable F := sorry
/- Proof strategy: unfold `relativelyRepresentable.homProperty`. -/

namespace relativelyRepresentable

/-- A relatively representable morphism has representable canonical base change along every
slice morphism. This named elimination API avoids unfolding `relativelyRepresentable` in
downstream statements. -/
theorem baseChange.isRepresentable
    {X Y : Groupoids C} {F : X ⟶ Y} (hF : relativelyRepresentable F)
    {U : C} (G : slice U ⟶ Y) :
    IsRepresentable (baseChange F G) := sorry

/-- The forward morphism of a bicategorical equivalence is relatively representable.

Together with `comp_mem`, this is the atomic endpoint-transport API: applications can pre- or
postcompose a relatively representable morphism with an equivalence without rebuilding its slice
base changes. -/
@[stacks 02Y7 "equivalence morphisms are relatively representable"]
theorem ofEquivalence {X Y : Groupoids C} (e : X ≌ Y) :
    relativelyRepresentable e.hom := sorry
/- Proof strategy: base-change `e.hom` along a slice morphism. The resulting first projection is
equivalent over the slice base to that slice fibration, hence is representable by
`slice.isRepresentable` and equivalence transport. -/

/-- Identity morphisms of categories fibred in groupoids are relatively representable. -/
theorem id_mem (X : Groupoids C) :
    relativelyRepresentable (𝟙 X) := sorry
/- Proof strategy: identify every base change of `𝟙 X` with the corresponding slice fibration
and transport representability across that bicategorical equivalence. -/

/-- Relative representability is stable under horizontal composition. -/
theorem comp_mem {X Y Z : Groupoids C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : relativelyRepresentable F) (hG : relativelyRepresentable G) :
    relativelyRepresentable (F ≫ G) := sorry
/- Proof strategy: express a base change of `F ≫ G` as the iterated base change first by `G`
and then by `F`; use `hG` to replace the first stage by a slice and apply `hF`, transporting
representability across the canonical associativity comparison. -/

/-- Relatively representable `1`-morphisms form a multiplicative bicategorical hom property. -/
instance homProperty.isMultiplicative :
    (relativelyRepresentable.homProperty (C := C)).IsMultiplicative := sorry
/- Proof strategy: use `id_mem` and `comp_mem` for the two class fields. -/

/-- Relative representability is stable under arbitrary bicategorical base change. -/
instance homProperty.BaseChange.isStable :
    (relativelyRepresentable.homProperty (C := C)).IsStableUnderBaseChange := sorry
/- Proof strategy: for a bilimit pseudopullback of `F : X ⟶ S` and a relatively representable
`G : Y ⟶ S`, base-change the first projection by a slice leg into its source. Reassociate the
resulting iterated pseudopullback with the base change of `G` along the composite slice leg
`slice U ⟶ X ⟶ S`, then transport representability across the canonical equivalence. -/

/-- Relative representability is invariant under isomorphism of parallel `1`-morphisms,
uniformly in their source and target. -/
instance homProperty.isClosedUnderIsomorphisms :
    (relativelyRepresentable.homProperty (C := C)).IsClosedUnderIsomorphisms := sorry
/- Proof strategy: whisker the given invertible `2`-cell with every slice leg, use the induced
isomorphism between the two base changes, and transport `IsRepresentable` across the resulting
bicategorical equivalence. -/

end relativelyRepresentable

end FiberedCategoryOver.Groupoids

end CategoryTheory
