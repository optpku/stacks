module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Operations on relative dimension

This leaf contains the base-change and composition API for bounded and fixed
relative dimensions.  The basic definitions remain in the parent leaf so
consumers that only state a dimension condition do not import operation rules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Relative dimension is preserved by arbitrary scheme base change. -/
@[stacks 02NK]
theorem relativeDimension_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ} [RelativeDimension f d] :
    RelativeDimension (pullback.snd f g) d := sorry

/-- A base change of a morphism of fixed relative dimension has that same
relative dimension. -/
@[stacks 02NK]
instance instRelativeDimensionPullbackSndOfRelativeDimension {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ} [RelativeDimension f d] :
    RelativeDimension (pullback.snd f g) d := relativeDimension_baseChange f g

/-- Fixed relative dimension is stable under arbitrary pullback squares of schemes. -/
instance instRelativeDimensionIsStableUnderBaseChange (r : ℕ) :
    MorphismProperty.IsStableUnderBaseChange
      (fun (_ _ : Scheme.{u}) f ↦ RelativeDimension f r) := sorry

/-- An upper relative-dimension bound is preserved by arbitrary scheme base
change. -/
@[stacks 02NK]
theorem relativeDimensionLE_baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ} [RelativeDimensionLE f d] :
    RelativeDimensionLE (pullback.snd f g) d := sorry

/-- A base change of a bounded-relative-dimension morphism has the same bound. -/
@[stacks 02NK]
instance instRelativeDimensionLEPullbackSndOfRelativeDimensionLE {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ} [RelativeDimensionLE f d] :
    RelativeDimensionLE (pullback.snd f g) d := relativeDimensionLE_baseChange f g

/-- Relative-dimension upper bounds add under composition. -/
@[stacks 02NL]
theorem relativeDimensionLE_comp {X Y Z : Scheme.{u}} {d e : ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [RelativeDimensionLE f d] [RelativeDimensionLE g e] :
    RelativeDimensionLE (f ≫ g) (d + e) := sorry

/-- Fixed relative dimensions add under composition when the first morphism is
flat. -/
@[stacks 02NL]
theorem relativeDimension_comp_of_flat {X Y Z : Scheme.{u}} {d e : ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [RelativeDimension f d] [RelativeDimension g e] [Flat f] :
    RelativeDimension (f ≫ g) (d + e) := sorry

/-- The composite of a flat morphism of relative dimension `d` with a morphism of relative
dimension `e` canonically has relative dimension `d + e`. -/
instance instRelativeDimensionCompOfFlat {X Y Z : Scheme.{u}} {d e : ℕ}
    (f : X ⟶ Y) (g : Y ⟶ Z) [RelativeDimension f d] [RelativeDimension g e] [Flat f] :
    RelativeDimension (f ≫ g) (d + e) := relativeDimension_comp_of_flat f g

end AlgebraicGeometry.Scheme.Hom
