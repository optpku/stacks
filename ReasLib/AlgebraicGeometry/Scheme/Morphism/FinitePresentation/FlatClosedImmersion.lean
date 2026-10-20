module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat closed immersions of finite presentation

A flat closed immersion of finite presentation is the inclusion of an open and closed subscheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A flat closed immersion of finite presentation is an open immersion. -/
@[stacks 0819]
theorem isOpenImmersion_of_isClosedImmersion
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsClosedImmersion f)
    [Flat f] [Scheme.Hom.FinitePresentation f] :
    IsOpenImmersion f := by
  -- Local instance justification (proof-local temporary data): temporarily register `hf`
  -- so closed-immersion-derived APIs can use the explicit hypothesis.
  letI : IsClosedImmersion f := hf
  exact IsOpenImmersion.of_flat_of_mono f

/-- The image of a flat closed immersion of finite presentation is open and closed. -/
@[stacks 0819]
theorem isClopen_range_of_flat_closedImmersion
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsClosedImmersion f)
    [Flat f] [Scheme.Hom.FinitePresentation f] :
    IsOpen (Set.range f.base) ∧ IsClosed (Set.range f.base) := by
  -- Local instance justification (proof-local temporary data): temporarily register `hf`
  -- so closed-immersion-derived APIs can use the explicit hypothesis.
  letI : IsClosedImmersion f := hf
  -- Local instance justification (proof-local temporary data): temporarily register the derived
  -- open-immersion proof so the canonical `isOpenEmbedding` API is available.
  haveI : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact ⟨f.isOpenEmbedding.isOpen_range, f.isClosedEmbedding.isClosed_range⟩

end AlgebraicGeometry
