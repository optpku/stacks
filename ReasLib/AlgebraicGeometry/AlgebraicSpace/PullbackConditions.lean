/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Object properties of fibre products of algebraic spaces

Fibre products preserve decency, reasonableness, and property (β) when both
factors have the corresponding property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If `X` and `Z` are decent, then the vertex of an `IsPullback` square for
`f : X ⟶ Y` and `g : Z ⟶ Y` is decent. -/
theorem IsDecent.of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X} {pZ : P ⟶ Z}
    (sq : IsPullback pX pZ f g) [IsDecent X] [IsDecent Z] : IsDecent P :=
  sorry

/-- If `X` and `Z` are reasonable, then the vertex of an `IsPullback` square for
`f : X ⟶ Y` and `g : Z ⟶ Y` is reasonable. -/
theorem IsReasonable.of_isPullback {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X} {pZ : P ⟶ Z}
    (sq : IsPullback pX pZ f g) [IsReasonable X] [IsReasonable Z] :
    IsReasonable P :=
  sorry

/-- If `X` and `Z` have property (β), then the vertex of an `IsPullback` square
for `f : X ⟶ Y` and `g : Z ⟶ Y` has property (β). -/
theorem HasPropertyBeta.of_isPullback {S : Scheme.{u}}
    {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X}
    {pZ : P ⟶ Z} (sq : IsPullback pX pZ f g) [HasPropertyBeta X]
    [HasPropertyBeta Z] : HasPropertyBeta P :=
  sorry

/-- The fibre product of two decent algebraic spaces over any algebraic space
is decent. -/
instance instIsDecent_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsDecent X] [IsDecent Z] :
    IsDecent (pullback f g) :=
  IsDecent.of_isPullback (IsPullback.of_hasPullback f g)

/-- The fibre product of two reasonable algebraic spaces over any algebraic
space is reasonable. -/
instance instIsReasonable_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsReasonable X] [IsReasonable Z] :
    IsReasonable (pullback f g) :=
  IsReasonable.of_isPullback (IsPullback.of_hasPullback f g)

/-- The fibre product of two algebraic spaces with property (β) over any
algebraic space has property (β). -/
instance instHasPropertyBeta_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPropertyBeta X] [HasPropertyBeta Z] :
    HasPropertyBeta (pullback f g) :=
  HasPropertyBeta.of_isPullback (IsPullback.of_hasPullback f g)

end AlgebraicGeometry.AlgebraicSpace
