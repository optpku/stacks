module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Order.Closure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturationAxiom

/-!
# Saturation of a morphism property

The saturation of `S : MorphismProperty C` consists of the morphisms sent to isomorphisms by the
canonical localization functor `S.Q`.  This operation is packaged as a `ClosureOperator`; its
fixed points are the saturated morphism properties.

The construction is meaningful without a calculus of fractions.  The two-sided description and
the inheritance of fraction calculi are exposed separately under their precise additional
hypotheses.
-/

@[expose] public section

universe v v₂ u w

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/- `saturation` below owns its computational map directly. Its three construction laws are
implementation details; downstream mathematics should use the generic `ClosureOperator`
API. -/

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The explicit localization-inversion operation is monotone in the morphism property. -/
theorem saturationMonotone :
    Monotone (fun S : MorphismProperty C =>
      (isomorphisms S.Localization).inverseImage S.Q) := sorry
/- Proof strategy: for `S ≤ T`, factor `T.Q` through the localization at `S`. The comparison
functor carries every morphism inverted by `S.Q` to an isomorphism, and the canonical comparison
with `T.Q` reflects membership in the localization-inversion operation for `T`. -/

/-- Every morphism property is contained in its explicit localization-inversion operation. -/
theorem leSaturation (S : MorphismProperty C) :
    S ≤ (isomorphisms S.Localization).inverseImage S.Q := sorry
/- Proof strategy: this is exactly `S.Q_inverts`, viewed as the inclusion of `S` in the inverse
image of the isomorphism property along `S.Q`. -/

/-- Applying the explicit localization-inversion operation twice has no further effect. -/
theorem saturationIdempotent (S : MorphismProperty C) :
    let T : MorphismProperty C := (isomorphisms S.Localization).inverseImage S.Q
    (isomorphisms T.Localization).inverseImage T.Q = T := sorry
/- Proof strategy: localizing at the morphisms already inverted by `S.Q` has the same universal
property as localizing at `S`. Compare both canonical localization models, use preservation and
reflection of isomorphisms by the comparison equivalence for one inclusion, and use
`leSaturation` for the other. -/

end Implementation

/-- Saturation is the closure operator sending a morphism property `S` to the morphisms carried
to isomorphisms by the canonical localization functor `S.Q`.

The two-sided description and the inheritance of fraction calculi are established under their
respective hypotheses. -/
@[stacks 05Q9 "saturation closure operator by the canonical localization"]
def saturation : ClosureOperator (MorphismProperty C) where
  toFun := fun S => (isomorphisms S.Localization).inverseImage S.Q
  monotone' := Implementation.saturationMonotone
  le_closure' := Implementation.leSaturation
  idempotent' := Implementation.saturationIdempotent

/-- Evaluation of the saturation closure operator in its canonical localization model. -/
@[simp]
theorem saturation.apply (S : MorphismProperty C) :
    (saturation (C := C)) S = (isomorphisms S.Localization).inverseImage S.Q := sorry
/- Proof strategy: unfold the explicit computational field of `saturation`. -/

/-- Membership in `saturation S` means that the canonical localization sends the morphism to an
isomorphism. -/
@[simp]
theorem saturation.mem_iff (S : MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    (saturation (C := C) S) f ↔ IsIso (S.Q.map f) := sorry
/- Proof strategy: rewrite with `saturation.apply` and unfold membership in `inverseImage` and
`isomorphisms`. -/

/-- Membership in `saturation S` is independent of the chosen localization model. -/
theorem saturation.mem_iff_of_isLocalization (S : MorphismProperty C)
    {D : Type w} [Category.{v₂} D] (L : C ⥤ D) [L.IsLocalization S]
    {X Y : C} (f : X ⟶ Y) :
    (saturation (C := C) S) f ↔ IsIso (L.map f) := sorry
/- Proof strategy: compare `L` with `S.Q` using
`Localization.equivalenceFromModel L S` and
`Localization.qCompEquivalenceFromModelFunctorIso L S`; equivalences and naturally isomorphic
functors preserve and reflect isomorphisms. -/

variable (S : MorphismProperty C)

/-- Assuming both calculi of fractions, a morphism lies in `saturation S` exactly when it admits
a postcomposition and a precomposition lying in `S`. -/
theorem saturation.mem_iff_two_sided [S.HasLeftCalculusOfFractions]
    [S.HasRightCalculusOfFractions] {X Y : C} (f : X ⟶ Y) :
    (saturation (C := C) S) f ↔
      ∃ (Z₁ Z₂ : C) (g : Y ⟶ Z₁) (h : Z₂ ⟶ X), S (f ≫ g) ∧ S (h ≫ f) := sorry
/- Proof strategy: represent the inverse of `S.Q.map f` once by a left fraction and once by a
right fraction, then clear denominators with `map_eq_iff_postcomp` and
`map_eq_iff_precomp`. Conversely, the two composite witnesses supply a right inverse and a left
inverse for `S.Q.map f`, hence an `IsIso` instance. -/

/-- The left calculus of fractions passes from `S` to `saturation S`. -/
instance saturation.left.hasCalculusOfFractions [S.HasLeftCalculusOfFractions] :
    ((saturation (C := C)) S).HasLeftCalculusOfFractions := sorry
/- Proof strategy: represent the required localized arrows by left fractions over `S`. For Ore
squares and cancellation, clear the remaining equality with `map_eq_iff_postcomp`; each resulting
denominator belongs to `S`, hence to `saturation S` by extensivity. -/

/-- The right calculus of fractions passes from `S` to `saturation S`. -/
instance saturation.right.hasCalculusOfFractions [S.HasRightCalculusOfFractions] :
    ((saturation (C := C)) S).HasRightCalculusOfFractions := sorry
/- Proof strategy: dualize `saturation.left.hasCalculusOfFractions`, using right-fraction
representatives and `map_eq_iff_precomp`; extensivity again puts every old denominator in
`saturation S`. -/

/-- `saturation S` satisfies the saturation axiom. -/
instance saturation.hasSaturationAxiom :
    ((saturation (C := C)) S).HasSaturationAxiom := sorry
/- Proof strategy: rewrite `saturation.apply`; the result is the canonical
`HasSaturationAxiom.inverseImage` instance applied to the isomorphism property and `S.Q`. -/

/-- For a morphism property with both calculi of fractions, being a fixed point of `saturation`
is equivalent to satisfying the saturation axiom. -/
theorem saturation.isClosed_iff [S.HasLeftCalculusOfFractions]
    [S.HasRightCalculusOfFractions] :
    (saturation (C := C)).IsClosed S ↔ S.HasSaturationAxiom := sorry
/- Proof strategy: if `S` is fixed, transport `saturation.hasSaturationAxiom S` across
`ClosureOperator.IsClosed.closure_eq`. Conversely, use
`saturation.mem_iff_two_sided`: the saturation axiom applied to `h`, `f`, and `g` proves
`saturation S ≤ S`, while `saturation.le_closure S` supplies the reverse inclusion. -/

/-- Among morphism properties with both calculi and the saturation axiom, `saturation S` is the
least one containing `S`. -/
theorem saturation.le_iff [S.HasLeftCalculusOfFractions]
    [S.HasRightCalculusOfFractions] {T : MorphismProperty C}
    [T.HasLeftCalculusOfFractions] [T.HasRightCalculusOfFractions]
    [T.HasSaturationAxiom] :
    (saturation (C := C)) S ≤ T ↔ S ≤ T := sorry
/- Proof strategy: the forward implication composes the assumed inclusion with
`saturation.le_closure S`. For the reverse implication, turn the three instances on `T` into
the fixed-point fact given by `saturation.isClosed_iff`, then apply
`saturation.closure_min`. -/

end MorphismProperty
end CategoryTheory
