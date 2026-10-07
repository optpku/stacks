module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.RingTheory.Flat.LocallyNilpotent.Fiber

/-!
# Flatness across thickenings

This file records flatness and stalkwise finiteness consequences for cartesian
commutative diagrams of thickenings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsThickening

/-- In a cartesian commutative diagram of thickenings, flatness of the closed-fiber
morphism lifts to the ambient morphism under the stated finiteness hypotheses. -/
@[stacks 0CF3]
theorem flatAmbient
    {X X' Y Y' S S' : Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [IsThickening iX] [IsThickening iY] [IsThickening iS]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY') :
    Flat f' := sorry

/-- In a cartesian commutative diagram of thickenings, the target structure morphism
is flat at every point in the image of the ambient morphism. -/
@[stacks 0CF3]
theorem flatAtTarget
    {X X' Y Y' S S' : Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [IsThickening iX] [IsThickening iY] [IsThickening iS]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY') :
    ∀ y' : Y', y' ∈ Set.range f' → pY'.flatAt y' := sorry

/-- In a cartesian commutative diagram of thickenings, the target structure morphism
induces an essentially finitely presented map on stalks at every point in the image of
the ambient morphism. -/
@[stacks 0CF3]
theorem essFinitePresentationAtTarget
    {X X' Y Y' S S' : Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [IsThickening iX] [IsThickening iY] [IsThickening iS]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY') :
    ∀ y' : Y', y' ∈ Set.range f' →
      (pY'.stalkMap y').hom.EssFinitePresentation := sorry

end AlgebraicGeometry.IsThickening

namespace AlgebraicGeometry.IsFiniteOrderThickening

/-- In a cartesian commutative diagram of thickenings over a finite-order thickening,
flatness of the closed-fiber morphism lifts to the ambient morphism. -/
@[stacks 06AF]
theorem flatAmbient
    {X X' Y Y' S S' : Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iS]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY') :
    Flat f' := sorry

/-- In a cartesian commutative diagram of thickenings over a finite-order thickening,
the target structure morphism is flat at every point in the image of the ambient morphism. -/
@[stacks 06AF]
theorem flatAtTarget
    {X X' Y Y' S S' : Scheme.{u}}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iS : S ⟶ S'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ S} {pX' : X' ⟶ S'} {pY : Y ⟶ S} {pY' : Y' ⟶ S'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iS]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iS pX')
    (pullbackY : IsPullback pY iY iS pY') :
    ∀ y' : Y', y' ∈ Set.range f' → pY'.flatAt y' := sorry

end AlgebraicGeometry.IsFiniteOrderThickening
