/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Fibre products of decent, reasonable, and property (β) algebraic spaces

If `X` and `Z` are decent, reasonable, or have property (β), then the fibre
product of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` of algebraic spaces has the
same object property. No hypothesis is imposed on `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.17.7 (1): If `X` and `Z` are decent algebraic spaces over a scheme `S`,
then the fibre product `pullback f g` of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` is
decent. -/
@[stacks 0ABZ]
instance instIsDecent_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsDecent X] [IsDecent Z] [HasPullback f g] :
    IsDecent (pullback f g) :=
  sorry

/-- Lemma 68.17.7 (2): If `X` and `Z` are reasonable algebraic spaces over a scheme
`S`, then the fibre product `pullback f g` of morphisms `f : X ⟶ Y` and
`g : Z ⟶ Y` is reasonable. -/
@[stacks 0ABZ]
instance instIsReasonable_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsReasonable X] [IsReasonable Z] [HasPullback f g] :
    IsReasonable (pullback f g) :=
  sorry

/-- Lemma 68.17.7 (3): If `X` and `Z` have property (β) of Lemma 68.5.1, then the
fibre product `pullback f g` of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` has
property (β). -/
@[stacks 0ABZ]
instance instHasPropertyBeta_pullback {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPropertyBeta X] [HasPropertyBeta Z]
    [HasPullback f g] : HasPropertyBeta (pullback f g) :=
  sorry

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

end AlgebraicGeometry.AlgebraicSpace
