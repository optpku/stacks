module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Immersion

/-!
# Operations on finite-type scheme morphisms

This module collects the closure operations for the project-level
`Scheme.Hom.FiniteType` class.  Its local component is mathlib's
`LocallyOfFiniteType`, while the global quasi-compact component is supplied by the same operation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Finite-type scheme morphisms form a morphism property stable under composition. -/
instance finiteType_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @FiniteType := sorry

/-- The composite of two finite-type scheme morphisms is finite type. -/
@[stacks 01T3]
theorem FiniteType.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : FiniteType f) (hg : FiniteType g) :
    FiniteType (f ≫ g) := sorry

/-- Finite-type scheme morphisms are closed under composition. -/
@[stacks 01T3, instance]
instance finiteType_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FiniteType f] [FiniteType g] :
    FiniteType (f ≫ g) := sorry

/-- Finite-type scheme morphisms form a morphism property stable under base change. -/
instance finiteType_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @FiniteType := sorry

/-- The left pullback projection is finite type when the right morphism is finite type. -/
theorem FiniteType.pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) {g : S' ⟶ S}
    (hg : FiniteType g) :
    FiniteType (pullback.fst f g) := sorry

/-- Pulling a finite-type right morphism back along an arbitrary morphism gives a finite-type
left projection. -/
instance finiteType_pullback_fst
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [FiniteType g] :
    FiniteType (pullback.fst f g) := sorry

/-- Every base change of a finite-type scheme morphism is finite type. -/
@[stacks 01T4]
theorem FiniteType.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : FiniteType f) (g : S' ⟶ S) :
    FiniteType (pullback.snd f g) := sorry

/-- The pullback projection obtained by base changing a finite-type morphism is finite type. -/
@[stacks 01T4, instance]
instance finiteType_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [FiniteType f] :
    FiniteType (pullback.snd f g) := sorry

end AlgebraicGeometry.Scheme.Hom
