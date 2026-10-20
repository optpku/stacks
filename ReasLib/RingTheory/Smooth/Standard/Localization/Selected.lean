module

public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import ReasLib.Algebra.Module.StableFree
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Selected standard elements and principal localizations

This leaf relates embedding-indexed standard data and the global standard
predicates to principal localizations. It also owns the presentation-independent
eventual-power converses.
-/

@[expose] public section

universe u v w t

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace Presentation.IsElementaryFor

variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- Selected elementary data in a finite presentation makes the corresponding
principal localization standard smooth. -/
@[stacks 07EZ "selected elementary standard localization"]
theorem isStandardSmoothAway
    {P : Presentation R A ι σ} {a : A} {c : ℕ}
    {cols : Fin c ↪ ι} {rows : Fin c ↪ σ}
    (h : P.IsElementaryFor a cols rows) :
    IsStandardSmooth R (Localization.Away a) := sorry

end Presentation.IsElementaryFor

namespace Presentation.IsStrictlyFor

variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- Selected strict data in a finite presentation makes the corresponding
principal localization smooth. -/
@[stacks 07EZ "selected strictly standard localization"]
theorem smoothAway
    {P : Presentation R A ι σ} {a : A} {c : ℕ} {rows : Fin c ↪ σ}
    (h : P.IsStrictlyFor a rows) :
    Smooth R (Localization.Away a) := sorry

/-- The Kähler differentials after localizing away from selected strict data
are stably free. -/
@[stacks 07EZ "selected strictly standard localization"]
theorem stablyFree_kaehlerDifferential_away
    {P : Presentation R A ι σ} {a : A} {c : ℕ} {rows : Fin c ↪ σ}
    (h : P.IsStrictlyFor a rows) :
    Module.StablyFree (Localization.Away a) Ω[Localization.Away a⁄R] := sorry

end Presentation.IsStrictlyFor

namespace IsElementaryStandard

/-- Localizing away from an elementary standard element gives a standard
smooth algebra. -/
@[stacks 07EZ "elementary standard localization"]
theorem isStandardSmoothAway {a : A} (h : IsElementaryStandard R a) :
    IsStandardSmooth R (Localization.Away a) := sorry

end IsElementaryStandard

namespace IsStrictlyStandard

/-- Localizing away from a strictly standard element gives a smooth algebra. -/
@[stacks 07EZ "strictly standard localization"]
theorem smoothAway {a : A} (h : IsStrictlyStandard R a) :
    Smooth R (Localization.Away a) := sorry

/-- The Kähler differentials of the localization away from a strictly standard element are
stably free. -/
@[stacks 07EZ "strictly standard localization"]
theorem stablyFree_kaehlerDifferential_away {a : A} (h : IsStrictlyStandard R a) :
    Module.StablyFree (Localization.Away a) Ω[Localization.Away a⁄R] := sorry

/-- If a finitely presented algebra is smooth away from `a` and its localized Kähler
differentials are stably free, sufficiently large powers of `a` are strictly standard. -/
@[stacks 07EZ "eventual strictly standard powers"]
theorem eventually_pow
    [FinitePresentation R A] (a : A)
    [hsmooth : Smooth R (Localization.Away a)]
    (hstablyFree : Module.StablyFree (Localization.Away a) Ω[Localization.Away a⁄R]) :
    ∀ᶠ e : ℕ in Filter.atTop, IsStrictlyStandard R (a ^ e) := sorry

end IsStrictlyStandard

namespace IsElementaryStandard

/-- For a finitely presented algebra, standard smoothness after inverting `a`
eventually makes powers of `a` elementary standard. -/
@[stacks 07EZ "eventual elementary standard powers"]
theorem eventually_pow
    [FinitePresentation R A] (a : A)
    [h : IsStandardSmooth R (Localization.Away a)] :
    ∀ᶠ e : ℕ in Filter.atTop, IsElementaryStandard R (a ^ e) := sorry

end IsElementaryStandard

end Algebra
