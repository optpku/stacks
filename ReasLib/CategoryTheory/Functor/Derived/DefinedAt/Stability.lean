module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic

/-!
# Stability of source-defined derived values

Source-definedness is inherited from terminal or initial localization denominators, transported
along localized morphisms and isomorphisms, and automatic for functors that invert the localized
class when the class admits the relevant calculus of fractions. These statements concern only the
essentially constant diagram, not a selected presentation.

The terminal/initial, isomorphism and `iff_of_mem` statements hold for an arbitrary class `S`:
they only reindex the comma category along `CostructuredArrow.mapIso` or
`StructuredArrow.mapIso`. The `of_isInvertedBy` statements need a calculus of fractions, as in
the source Situation 05S8 (a saturated multiplicative system). Without it they fail: let `D` have
objects `W, Y, X` and only the non-identity maps `s : W ⟶ Y` and `g : W ⟶ X`, let
`S = {identities, s}` and `F = S.Q`. The comma category over `S.Q.obj X` is the span
`(Y, (S.Q.map s)⁻¹ ≫ S.Q.map g) ← (W, S.Q.map g) → (X, 𝟙)`, and in the localization
`S.Q.obj X` has no morphism to `S.Q.obj W` or `S.Q.obj Y`. The stages `(X, 𝟙)` and `(Y, _)`
have no common successor, so neither satisfies the factorization clause for the other; at stage
`(W, _)` the clause for `(X, 𝟙)` would make `S.Q.obj X` a retract of `S.Q.obj W`. With a left
calculus of fractions the diagram is essentially constant with stage `(X, 𝟙)`, cocone point
`F.obj X` and legs given by the functor induced by `F` on the localization: every
`f : S.Q.obj Z ⟶ S.Q.obj X` is a left fraction `Z ⟶ X' ⟵ X`, and `(X', _)` is the required common
successor.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- A terminal object of the right-derived indexing category gives an essentially constant
presentation, hence source-definedness at `X`. -/
theorem RightDerived.DefinedAt.of_isTerminal
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    {d : CostructuredArrow S.Q (S.Q.obj X)} (hd : IsTerminal d) :
    RightDerived.DefinedAt F S X := sorry

/-- An initial object of the left-derived indexing category gives an essentially constant
presentation, hence source-definedness at `X`. -/
theorem LeftDerived.DefinedAt.of_isInitial
    (F : D ⥤ D') (S : MorphismProperty D) (X : D)
    {d : StructuredArrow (S.Q.obj X) S.Q} (hd : IsInitial d) :
    LeftDerived.DefinedAt F S X := sorry

/-- Source-definedness of a right-derived value is invariant along a morphism belonging to the
localized class. -/
theorem RightDerived.DefinedAt.iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    (f : X ⟶ Y) (hf : S f) :
    RightDerived.DefinedAt F S X ↔ RightDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a left-derived value is invariant along a morphism belonging to the
localized class. -/
theorem LeftDerived.DefinedAt.iff_of_mem
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    (f : X ⟶ Y) (hf : S f) :
    LeftDerived.DefinedAt F S X ↔ LeftDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a right-derived value is stable under isomorphism of the source
object. -/
theorem RightDerived.DefinedAt.of_iso
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    [RightDerived.DefinedAt F S X] (e : X ≅ Y) :
    RightDerived.DefinedAt F S Y := sorry

/-- Source-definedness of a left-derived value is stable under isomorphism of the source
object. -/
theorem LeftDerived.DefinedAt.of_iso
    (F : D ⥤ D') (S : MorphismProperty D) {X Y : D}
    [LeftDerived.DefinedAt F S X] (e : X ≅ Y) :
    LeftDerived.DefinedAt F S Y := sorry

/-- If `S` has a left calculus of fractions, a functor which inverts `S` has an essentially
constant right-derived indexing diagram at every object. -/
theorem RightDerived.DefinedAt.of_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) [S.HasLeftCalculusOfFractions] (X : D)
    (hF : S.IsInvertedBy F) :
    RightDerived.DefinedAt F S X := sorry

/-- If `S` has a right calculus of fractions, a functor which inverts `S` has an essentially
constant left-derived indexing diagram at every object. -/
theorem LeftDerived.DefinedAt.of_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) [S.HasRightCalculusOfFractions] (X : D)
    (hF : S.IsInvertedBy F) :
    LeftDerived.DefinedAt F S X := sorry


end CategoryTheory.Functor
