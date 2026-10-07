module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Lifted

/-!
# Universe-saturated relative representability

The fixed-base, heterogeneous-slice-leg variant of relative representability, its bicategorical
hom-property closure API, and comparison with the ordinary fixed-universe predicate. Concrete
base-change data lives in the neutral `Groupoids.SliceBaseChange` leaf.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/-- Heterogeneous-boundary relative representability for a universe-saturated owner. -/
@[stacks 02Y7 "heterogeneous relative representability"]
def relativelyRepresentable.overBase :
    MorphismProperty
      (Groupoids.{u, v, max w (max u v), max vS v} C) :=
  fun _ Y F ↦
    ∀ ⦃U : C⦄ (G : (slice U).toBasedCategory ⥤ᵇ Y.toBasedCategory),
      IsRepresentable.Lifted.{max u v, v, max w vS, vS}
        (baseChange.overBase F G)

/-- The bicategorical hom-property owner for heterogeneous relative representability. -/
@[stacks 02Y7 "hom-property of heterogeneous relatively representable morphisms"]
def relativelyRepresentable.overBase.homProperty :
    Bicategory.HomProperty
      (fun X : Groupoids.{u, v, max w (max u v), max vS v} C ↦ X) :=
  fun _ _ F ↦ relativelyRepresentable.overBase F

/- Axiom audit: these owners are predicate-valued. Any `sorryAx` is inherited only through
the Prop-valued fibredness and coherence fields of `baseChange` and `fstGroupoids`. -/

/-- The heterogeneous hom-property owner computes to its predicate presentation. -/
@[simp]
theorem relativelyRepresentable.overBase.homProperty_apply
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C} (F : X ⟶ Y) :
    relativelyRepresentable.overBase.homProperty X Y F ↔
      relativelyRepresentable.overBase F := sorry

namespace relativelyRepresentable.overBase

/-- A heterogeneous relatively representable morphism has representable pseudo-pullback along
every based morphism from a canonical slice fibration. -/
theorem baseChange.isRepresentable
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C}
    {F : X ⟶ Y} (hF : relativelyRepresentable.overBase F)
    {U : C} (G : (slice U).toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    IsRepresentable.Lifted.{max u v, v, max w vS, vS}
      (baseChange.overBase F G) := sorry

/-- The forward morphism of a bicategorical equivalence in a saturated owner is heterogeneously
relatively representable.  This is the resizing-boundary companion of
`relativelyRepresentable.ofEquivalence`. -/
@[stacks 02Y7 "heterogeneous equivalence morphisms"]
theorem ofEquivalence
    {X Y : Groupoids.{u, v, max w (max u v), max vS v} C}
    (e : X ≌ Y) :
    relativelyRepresentable.overBase e.hom := sorry
/- Proof strategy: each based slice pullback of `e.hom` is equivalent over its slice base to the
canonical slice fibration; use lifted representability of that slice and transport across the
resulting based equivalence. -/

/-- Identity morphisms satisfy heterogeneous-boundary relative representability. -/
theorem id_mem
    (X : Groupoids.{u, v, max w (max u v), max vS v} C) :
    relativelyRepresentable.overBase (𝟙 X) := sorry

/-- Heterogeneous-boundary relative representability is stable under composition. -/
theorem comp_mem
    {X Y Z : Groupoids.{u, v, max w (max u v), max vS v} C}
    {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : relativelyRepresentable.overBase F)
    (hG : relativelyRepresentable.overBase G) :
    relativelyRepresentable.overBase (F ≫ G) := sorry

/-- Heterogeneous relatively representable morphisms form a multiplicative hom property. -/
instance homProperty.isMultiplicative :
    (relativelyRepresentable.overBase.homProperty.{u, v, w, vS}
      (C := C)).IsMultiplicative := sorry

/-- Heterogeneous relative representability is stable under bicategorical base change. -/
instance homProperty.BaseChange.isStable :
    (relativelyRepresentable.overBase.homProperty.{u, v, w, vS}
      (C := C)).IsStableUnderBaseChange := sorry

/-- Heterogeneous relative representability is invariant under parallel isomorphism,
uniformly in source and target. -/
instance homProperty.isClosedUnderIsomorphisms :
    (relativelyRepresentable.overBase.homProperty.{u, v, w, vS}
      (C := C)).IsClosedUnderIsomorphisms := sorry

end relativelyRepresentable.overBase

namespace relativelyRepresentable

/-- In the ordinary fixed owner, ordinary and heterogeneous relative representability agree. -/
@[stacks 02Y7 "ordinary/heterogeneous slice-leg bridge"]
theorem iff_overBase
    {X Y : Groupoids C} (F : X ⟶ Y) :
    relativelyRepresentable F ↔
      relativelyRepresentable.overBase.{u, v, 0, 0} F := sorry

end relativelyRepresentable

end FiberedCategoryOver.Groupoids

end CategoryTheory
