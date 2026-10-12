/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A localized affine-space morphism

This file constructs the morphism from the spectrum of
`ℂ[x, t, 1 / (x * t)]` to the spectrum of `ℂ[t]`, together with an explicit
section over the basic open where `t` is invertible.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace AlgebraicGeometry.LocalizationAwayXT

/-- The polynomial ring `ℂ[t]` underlying the affine base scheme. -/
abbrev BaseRing : Type :=
  Polynomial ℂ

/-- The iterated polynomial ring `(ℂ[t])[x]` underlying the total space. -/
abbrev PolyRing : Type :=
  Polynomial BaseRing

/-- The base coordinate `t` in `ℂ[t]`. -/
def t : BaseRing :=
  Polynomial.X

/-- The fiber coordinate `x` in `(ℂ[t])[x]`. -/
def x : PolyRing :=
  Polynomial.X

/-- The element `x * t` of `(ℂ[t])[x]` that is inverted. -/
def xt : PolyRing :=
  Polynomial.C t * x

/-- The localized coordinate ring `ℂ[x, t, 1 / (x * t)]`. -/
abbrev CoordRing : Type :=
  Localization.Away xt

/-- Evaluation of `(ℂ[t])[x]` at `x = 1`, with values in `ℂ[t]`. -/
def evalAtOne : PolyRing →+* BaseRing :=
  Polynomial.evalRingHom 1

/-- Evaluation at `x = 1` sends the inverted element `x * t` to `t`. -/
theorem evalAtOne_xt : evalAtOne xt = t := sorry

/-- The localization map induced by evaluation at `x = 1`. -/
def localSectionRingHom : CoordRing →+* Localization.Away (evalAtOne xt) :=
  Localization.awayMap evalAtOne xt

/-- The affine base scheme `Spec(ℂ[t])`. -/
abbrev base : Scheme :=
  Spec (CommRingCat.of BaseRing)

/-- The affine total space `Spec(ℂ[x, t, 1 / (x * t)])`. -/
abbrev scheme : Scheme :=
  Spec (CommRingCat.of CoordRing)

/-- The ring homomorphism from the base coordinate ring to the localized ring. -/
def toBaseRingHom : BaseRing →+* CoordRing :=
  (algebraMap PolyRing CoordRing).comp (algebraMap BaseRing PolyRing)

/-- The affine morphism from the total space to the base scheme. -/
def toBase : scheme ⟶ base :=
  Spec.map (CommRingCat.ofHom toBaseRingHom)

/-- The open immersion of `Spec(ℂ[t][1 / t])` into the base scheme. -/
abbrev awayUnit : Spec (CommRingCat.of (Localization.Away (evalAtOne xt))) ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap BaseRing (Localization.Away (evalAtOne xt))))

/-- The basic open of the base scheme on which `t` is invertible. -/
abbrev unitOpen : base.Opens :=
  awayUnit.opensRange

/-- The explicit morphism from the open `unitOpen` to the total space. -/
def localSection : unitOpen.toScheme ⟶ scheme :=
  awayUnit.isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom localSectionRingHom)

/-- The basic open `unitOpen` is nonempty. -/
theorem unitOpen_nonempty : Nonempty unitOpen := sorry

/-- The explicit morphism `localSection` is a section of `toBase` over `unitOpen`. -/
theorem localSection_comp_toBase : localSection ≫ toBase = unitOpen.ι := sorry

/-- The affine morphism `toBase` has no section over the whole base scheme. -/
theorem not_exists_section :
    ¬ ∃ σ : base ⟶ scheme, σ ≫ toBase = 𝟙 base := sorry

/-- There is a nonempty open of the base scheme over which `toBase` has a section. -/
theorem exists_rational_section :
    ∃ U : base.Opens, Nonempty U ∧ ∃ σ : U.toScheme ⟶ scheme, σ ≫ toBase = U.ι := sorry

end AlgebraicGeometry.LocalizationAwayXT
