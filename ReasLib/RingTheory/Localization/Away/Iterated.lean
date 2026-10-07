module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterated principal localizations

This leaf owns the canonical comparison data for localizing
`Localization.Away f` again at the image of `g`, and for identifying that
chart with `Localization.Away (f * g)`.

@stack 051T
-/

@[expose] public section

universe u

namespace Localization.Away.Iterated

variable {R : Type u} [CommSemiring R]

/-- The image of `g` in the principal localization of `R` away from `f`. This
is the distinguished element for the second localization in an iterated
principal-localization chart. -/
@[stacks 051T "iterated principal-localization coefficient"]
abbrev coefficient (f g : R) : Localization.Away f :=
  algebraMap R (Localization.Away f) g

/-- The ring obtained by localizing `Localization.Away f` away from the image
of `g`. -/
@[stacks 051T "iterated principal-localization coefficient chart"]
abbrev coefficientChart (f g : R) : Type u :=
  Localization.Away (coefficient f g)

/-- The explicit algebra action on `Localization.Away (f * g)` induced by the
canonical map from `Localization.Away f`. This is not a global instance because
it can coincide with a different ambient algebra action. -/
@[stacks 051T "iterated principal-localization right action"]
noncomputable abbrev rightAlgebra (f g : R) :
    Algebra (Localization.Away f) (Localization.Away (f * g)) :=
  (IsLocalization.Away.awayToAwayRight
    (P := Localization.Away (f * g)) f g).toAlgebra

/-- The explicit algebra action on `Localization.Away (f * g)` induced by the
canonical map from `Localization.Away g`. This is the left-handed counterpart
of `rightAlgebra`. -/
@[stacks 051T "iterated principal-localization left action"]
noncomputable abbrev leftAlgebra (f g : R) :
    Algebra (Localization.Away g) (Localization.Away (f * g)) :=
  (IsLocalization.Away.awayToAwayLeft
    (P := Localization.Away (f * g)) g f).toAlgebra

/-- The canonical right-handed iterated principal-localization action forms a scalar tower over
the original ring. -/
@[stacks 051T "iterated principal-localization right scalar tower"]
theorem rightAlgebra_isScalarTower (f g : R) :
    -- Local instance justification (noncanonical choice): select the named right action.
    letI : Algebra (Localization.Away f) (Localization.Away (f * g)) := rightAlgebra f g
    IsScalarTower R (Localization.Away f) (Localization.Away (f * g)) := sorry

/-- The canonical left-handed iterated principal-localization action forms a scalar tower over
the original ring. -/
@[stacks 051T "iterated principal-localization left scalar tower"]
theorem leftAlgebra_isScalarTower (f g : R) :
    -- Local instance justification (noncanonical choice): select the named left action.
    letI : Algebra (Localization.Away g) (Localization.Away (f * g)) := leftAlgebra f g
    IsScalarTower R (Localization.Away g) (Localization.Away (f * g)) := sorry

/-- The canonical `Localization.Away f`-algebra structure on the coefficient
chart forms a scalar tower over `R`. -/
@[stacks 051T "iterated principal-localization coefficient scalar tower"]
theorem coefficientChartIsScalarTower (f g : R) :
    IsScalarTower R (Localization.Away f) (coefficientChart f g) := sorry

/-- Under the right-handed iterated action, `Localization.Away (f * g)` is the
localization of `Localization.Away f` away from the image of `g`. -/
@[stacks 051T "iterated principal-localization coefficient owner"]
theorem coefficientIsLocalization (f g : R) :
    -- Local instance justification (noncanonical choice): use the right action for this localization.
    letI : Algebra (Localization.Away f) (Localization.Away (f * g)) := rightAlgebra f g
    IsLocalization.Away (coefficient f g) (Localization.Away (f * g)) := sorry

end Localization.Away.Iterated
