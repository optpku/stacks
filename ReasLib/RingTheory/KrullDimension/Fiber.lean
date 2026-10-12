/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Fiber.MinimalPrime
public import ReasLib.RingTheory.RingHom.Fiber.Local

@[expose] public section

/-!
# Krull dimension of local fibers

These statements compare a localization at a point of a ring map with the
local ring of the corresponding residue-field fiber.

@stack 00P2
@stack 00OL
@stack 00OM
@stack 0CWE
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The height defect of a prime along a ring map is the height of its contraction minus its own
height.  For a surjective presentation, this is the local codimension contributed by the
presentation kernel. -/
@[stacks 00P2 "prime height-defect support"]
noncomputable def primeHeightDefect (f : R →+* S) (q : PrimeSpectrum S) : ℕ∞ :=
  (PrimeSpectrum.comap f q).asIdeal.height - q.asIdeal.height

end RingHom

namespace Algebra.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- The finite-algebra zero-dimensionality statement is independent of any
   presentation or dimension comparison theorem, so it is owned at the
   local-fiber dimension layer. -/

/-- A local fiber of a finite algebra has Krull dimension zero. -/
@[stacks 00OL "finite local fiber has dimension zero"]
theorem ringKrullDim_eq_zero_of_moduleFinite
    [Module.Finite R S] (q : PrimeSpectrum S) :
    ringKrullDim (fiberLocalRingAt R S q) = 0 := sorry

/-- The Krull dimension of the local fiber ring equals the height of its canonical fiber
prime. -/
@[stacks 00OL "local fiber dimension as fiber-prime height"]
theorem ringKrullDim_fiberLocalRingAt_eq_height (q : PrimeSpectrum S) :
    ringKrullDim (fiberLocalRingAt R S q) =
      (fiberPrimeAt R S q).asIdeal.height := sorry

/-- A height-zero canonical fiber prime gives a zero-dimensional local fiber ring. -/
@[stacks 0CWE "height-zero fiber-prime dimension bridge"]
theorem ringKrullDim_fiberLocalRingAt_eq_zero_of_height_eq_zero
    (q : PrimeSpectrum S) (hq : (fiberPrimeAt R S q).asIdeal.height = 0) :
    ringKrullDim (fiberLocalRingAt R S q) = 0 := sorry

/-- A faithfully flat map has a point above every source prime whose canonical fiber prime has
height zero. -/
@[stacks 0CWE "height-zero point in a faithfully flat fiber"]
theorem exists_fiberPrimeAt_height_eq_zero
    [Module.FaithfullyFlat R S] (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum S,
      PrimeSpectrum.comap (algebraMap R S) q = p ∧
        (fiberPrimeAt R S q).asIdeal.height = 0 := sorry

/-- The quotient of `S_q` by the extension of `q ∩ R` has the same Krull dimension as the
canonical local fiber ring at `q`. -/
@[stacks 00OL "quotient-localization local-fiber dimension bridge"]
theorem krullDim_quotientLocalizationAtPrime_eq (q : PrimeSpectrum S) :
    ringKrullDim
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal))
            (Ideal.comap (algebraMap R S) q.asIdeal)) =
      ringKrullDim (fiberLocalRingAt R S q) := sorry

/-- The order height of the canonical fiber prime equals that of the corresponding point in the
raw prime-spectrum fiber over its contraction. -/
@[stacks 00OL "fiber-prime order-height bridge"]
theorem fiberPrimeAt_orderHeight_eq_preimageHeight (q : PrimeSpectrum S) :
    Order.height (fiberPrimeAt R S q) =
      Order.height
        (⟨q, rfl⟩ :
          (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R S) q}) := sorry

/-- The raw-fiber order-height comparison for `fiberPrimeAt` over an explicitly named
contraction point. -/
@[stacks 00OL "fiber-prime order-height bridge"]
theorem fiberPrimeAt_orderHeight_eq_preimageHeight_of_comap_eq
    {p : PrimeSpectrum R} (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Order.height (fiberPrimeAt R S q) =
      Order.height (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R S)) ⁻¹' {p}) := sorry

/-- For lying-over primes of a Noetherian ring map, the Krull dimension of the target
localization is bounded by the sum of the base-local and local-fiber dimensions. -/
@[stacks 00OM]
theorem krullDim_localizationAtPrime_le_add
    [IsNoetherianRing R] [IsNoetherianRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) ≤
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim (fiberLocalRingAt R S ⟨q, inferInstance⟩) := sorry

end Algebra.Fiber
