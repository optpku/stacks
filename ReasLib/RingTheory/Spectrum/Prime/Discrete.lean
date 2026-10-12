/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

@[expose] public section

/-!
# Discrete prime spectra from the Jacobson radical

This leaf packages the exact criterion relating a discrete prime spectrum to a
finite maximal spectrum and a locally nilpotent Jacobson radical.  The
topological and Krull-dimension consequences are explicit theorems rather than
global instances: their hypotheses are data of a particular argument and
cannot be inferred by typeclass search.
-/

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-! ### The finite-Jacobson criterion -/

namespace Jacobson

/-- A commutative ring has discrete prime spectrum exactly when its maximal
spectrum is finite and its Jacobson radical is locally nilpotent. -/
@[stacks 00JA "discrete spectrum criterion"]
theorem discreteTopology_iff_finite :
    DiscreteTopology (PrimeSpectrum R) ↔
      Finite (MaximalSpectrum R) ∧
        (Ring.jacobson R).IsLocallyNilpotent := sorry

/-- A finite maximal spectrum and a locally nilpotent Jacobson radical make
the prime spectrum discrete. -/
@[stacks 00JA "discrete spectrum from the Jacobson radical"]
theorem discreteTopology
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    DiscreteTopology (PrimeSpectrum R) := sorry

/-- A ring with finite maximal spectrum and locally nilpotent Jacobson radical
has Krull dimension at most zero. -/
@[stacks 00JA "Krull dimension from the Jacobson radical"]
theorem krullDimLE_zero
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    Ring.KrullDimLE 0 R := sorry

/-- Every prime ideal is maximal when the maximal spectrum is finite and the
Jacobson radical is locally nilpotent. -/
@[stacks 00JA "prime ideals are maximal"]
theorem isMaximal
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent)
    {I : Ideal R} (hI : I.IsPrime) :
    I.IsMaximal := sorry

end Jacobson

end PrimeSpectrum

namespace MaximalSpectrum

variable {R : Type u} [CommRing R]

/-! ### The localization-product equivalence -/

namespace Jacobson

/-- The canonical algebra equivalence from a ring with finite maximal
spectrum and locally nilpotent Jacobson radical to the product of its
localizations at maximal ideals. -/
@[stacks 00JA "maximal-spectrum localization product"]
noncomputable def toPiLocalizationEquiv
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    R ≃ₐ[R] MaximalSpectrum.PiLocalization R :=
  -- This proof-local instance selects the existing Mathlib equivalence; the
  -- Jacobson hypothesis is not a class and cannot support a global instance.
  letI : DiscreteTopology (PrimeSpectrum R) :=
    PrimeSpectrum.Jacobson.discreteTopology hjac
  MaximalSpectrum.toPiLocalizationEquiv R

/-- The forward algebra homomorphism of the localization-product equivalence
is the canonical map to the product of maximal localizations. -/
@[stacks 00JA "maximal-spectrum localization product specification", simp]
theorem toPiLocalizationEquiv_toAlgHom
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) :
    (toPiLocalizationEquiv hjac).toAlgHom =
      MaximalSpectrum.toPiLocalization R := sorry

/-- The localization-product equivalence sends an element to its canonical
family of images in the maximal localizations. -/
@[stacks 00JA "maximal-spectrum localization product application", simp]
theorem toPiLocalizationEquiv_apply
    [Finite (MaximalSpectrum R)]
    (hjac : (Ring.jacobson R).IsLocallyNilpotent) (x : R) :
    toPiLocalizationEquiv hjac x = algebraMap R _ x := sorry

end Jacobson

end MaximalSpectrum
