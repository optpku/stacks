/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic

@[expose] public section

/-!
# Associated-prime formulations of Japanese schemes

This module records the locally Noetherian stalkwise and unrestricted affine
associated-prime Japanese conditions, and the bridge from the affine condition
to the integral affine-local `Scheme.IsJapanese` predicate.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme satisfies the stalkwise associated-prime Japanese condition when
it is locally Noetherian and every associated-prime quotient of every stalk is
`N-2`. -/
def IsJapaneseAtStalkAssociatedPrimes (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧
    ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)),
      IsAssociatedPrime p.asIdeal (X.presheaf.stalk x) →
        IsN2Ring (X.presheaf.stalk x ⧸ p.asIdeal)

/-- A scheme satisfies the affine associated-prime Japanese condition when every
associated-prime quotient of every affine section ring is `N-2`. -/
@[stacks 033T]
def IsJapaneseAtAffineAssociatedPrimes (X : Scheme.{u}) : Prop :=
  ∀ (U : X.affineOpens) (p : PrimeSpectrum (Γ(X, U))),
    IsAssociatedPrime p.asIdeal (Γ(X, U)) →
      IsN2Ring (Γ(X, U) ⧸ p.asIdeal)

/-- The stalkwise associated-prime Japanese condition is equivalent to local
Noetherianity together with the `N-2` condition for every associated-prime
quotient of every stalk. -/
theorem isJapaneseAtStalkAssociatedPrimes_iff (X : Scheme.{u}) :
    IsJapaneseAtStalkAssociatedPrimes X ↔
      IsLocallyNoetherian X ∧
        ∀ (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)),
          IsAssociatedPrime p.asIdeal (X.presheaf.stalk x) →
            IsN2Ring (X.presheaf.stalk x ⧸ p.asIdeal) := sorry

/-- The affine associated-prime Japanese condition is equivalent to the `N-2`
condition for every associated-prime quotient of every affine section ring. -/
theorem isJapaneseAtAffineAssociatedPrimes_iff (X : Scheme.{u}) :
    IsJapaneseAtAffineAssociatedPrimes X ↔
      ∀ (U : X.affineOpens) (p : PrimeSpectrum (Γ(X, U))),
        IsAssociatedPrime p.asIdeal (Γ(X, U)) →
          IsN2Ring (Γ(X, U) ⧸ p.asIdeal) := sorry

namespace IsJapaneseAtAffineAssociatedPrimes

/-- On an integral scheme satisfying the affine associated-prime Japanese
condition, every nonempty affine open has `N-2` section ring. -/
theorem affineOpenSectionsIsN2Ring (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseAtAffineAssociatedPrimes X) (U : X.affineOpens) (hU : Nonempty U) :
    affineOpenSectionsIsN2Ring X U hU := sorry

/-- An integral scheme satisfying the affine associated-prime Japanese
condition is Japanese in the affine-open sense. -/
@[stacks 033T]
theorem isJapanese (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseAtAffineAssociatedPrimes X) :
    IsJapanese X := sorry

end IsJapaneseAtAffineAssociatedPrimes

variable (X : Scheme.{u}) [IsIntegral X]

/-- An integral scheme is Japanese exactly when every nonempty affine open has
`N-2` section ring. -/
@[stacks 033V]
theorem isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∀ U : X.affineOpens,
        ∀ hU : Nonempty U,
          affineOpenSectionsIsN2Ring X U hU := sorry

/-- An integral scheme is Japanese exactly when some affine open cover has
nonempty members with `N-2` section rings. -/
@[stacks 033V]
theorem isJapanese_iff_exists_affineOpenCover_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ∀ hU : Nonempty (𝒰.f i).opensRange,
            affineOpenSectionsIsN2Ring X
              ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩ hU := sorry

/-- An integral scheme is Japanese exactly when some open cover consists of
nonempty Japanese open subschemes. -/
@[stacks 033V]
theorem isJapanese_iff_exists_openCover_by_isJapanese :
    IsJapanese X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀,
          ∀ [Nonempty (𝒰.f i).opensRange],
            IsJapanese ((𝒰.f i).opensRange).toScheme := sorry

variable {X : Scheme.{u}} [IsIntegral X]

/-- A nonempty open subscheme of an integral Japanese scheme is Japanese. -/
@[stacks 033V]
theorem isJapanese_toScheme (hX : IsJapanese X) (U : X.Opens) [Nonempty U] :
    IsJapanese U.toScheme := sorry

end AlgebraicGeometry.Scheme
