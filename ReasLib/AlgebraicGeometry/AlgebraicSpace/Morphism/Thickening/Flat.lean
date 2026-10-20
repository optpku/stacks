/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder

/-!
# Flatness across thickenings of algebraic spaces

This file records flatness consequences for cartesian commutative diagrams of
thickenings of algebraic spaces.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsThickening

/-- In a cartesian commutative diagram of thickenings of algebraic spaces over
a scheme, a flat morphism between the closed fibers lifts to a flat ambient
morphism if the ambient source is flat and locally of finite presentation over
the base and the ambient target is locally of finite type over the base. -/
@[stacks 0CGW]
theorem flatAmbient
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    Flat f' := sorry

/-- In a cartesian commutative diagram of thickenings of algebraic spaces over
a scheme, suppose the ambient source is flat and locally of finite presentation
over the base, the ambient target is locally of finite type over the base, and
the morphism between the closed fibers is flat. Then the target structure
morphism is flat at every point in the image of the ambient morphism. -/
@[stacks 0CGW]
theorem flatAtTarget
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsThickening iB]
    [LocallyOfFiniteType pY'] [Flat pX'] [LocallyOfFinitePresentation pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y' := sorry

end AlgebraicGeometry.AlgebraicSpace.IsThickening

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- In a cartesian commutative diagram of thickenings of algebraic spaces over
a scheme, a flat morphism between the closed fibers lifts to a flat ambient
morphism if the base thickening has finite order and the ambient source is flat
over the thickened base. -/
@[stacks 0CG5]
theorem flatAmbient
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iB]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    Flat f' :=
  sorry

/-- In a cartesian commutative diagram of thickenings of algebraic spaces over
a scheme, suppose the base thickening has finite order, the ambient source is
flat over the thickened base, and the morphism between the closed fibers is flat.
Then the ambient target is flat over the thickened base at every point in the
image of the ambient morphism. -/
@[stacks 0CG5]
theorem flatAtTarget
    {S : Scheme.{u}} {X X' Y Y' B B' : AlgebraicSpace S}
    {iX : X ⟶ X'} {iY : Y ⟶ Y'} {iB : B ⟶ B'}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {pX : X ⟶ B} {pX' : X' ⟶ B'} {pY : Y ⟶ B} {pY' : Y' ⟶ B'}
    [IsThickening iX] [IsThickening iY] [IsFiniteOrderThickening iB]
    [Flat pX'] [Flat f]
    (sq : CommSq f iX iY f')
    (triangle : f ≫ pY = pX) (triangle' : f' ≫ pY' = pX')
    (pullbackX : IsPullback pX iX iB pX')
    (pullbackY : IsPullback pY iY iB pY') :
    ∀ y' : Points Y', y' ∈ Set.range (Points.map f') → FlatAt pY' y' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
