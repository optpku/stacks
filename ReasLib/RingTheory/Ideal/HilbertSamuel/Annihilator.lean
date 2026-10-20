module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Polynomial
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity
public import ReasLib.RingTheory.Module.Support.Annihilator
public import ReasLib.RingTheory.Module.Support.FiniteLength
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- For a finite module over a Noetherian local ring, finite colength of `I` on `M`
is equivalent to the corresponding condition after adjoining the annihilator, passing to
the quotient by the annihilator, restricting support to the closed point, bounding support
dimension by zero, or requiring finite module length. -/
theorem finiteColength_tfae [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (hproper : I + Module.annihilator R M ≠ ⊤) :
    List.TFAE
      [ (I + Module.annihilator R M).IsIdealOfDefinition
      , (I.map (Ideal.Quotient.mk (Module.annihilator R M))).radical =
          (IsLocalRing.maximalIdeal R).map
            (Ideal.Quotient.mk (Module.annihilator R M))
      , Module.support R (M ⧸ (I • ⊤ : Submodule R M)) ⊆
          {IsLocalRing.closedPoint R}
      , Module.supportDim R (M ⧸ (I • ⊤ : Submodule R M)) ≤ 0
      , Module.length R (M ⧸ (I • ⊤ : Submodule R M)) < ⊤
      ] := sorry

/-- Adjoining the annihilator of `M` to `I` does not change the submodule killed by any power
of the ideal. -/
theorem pow_smul_top_add_annihilator (I : Ideal R) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) =
      ((I + Module.annihilator R M) ^ n • ⊤ : Submodule R M) := sorry

/-- Powers of the image of `I` in `R ⧸ Module.annihilator R M`, restricted back to `R`, give
the same submodules of `M` as powers of `I`. -/
theorem pow_smul_top_quotientAnnihilator (I : Ideal R) (n : ℕ) :
    let A := R ⧸ Module.annihilator R M
    -- Local instance justification (search instability): the canonical quotient-annihilator action is intentionally selected locally.
    letI : Module A M := Module.quotientAnnihilator
    -- Local instance justification (search instability): the scalar tower is tied to the selected quotient-annihilator action.
    letI : IsScalarTower R A M :=
      Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
    Submodule.restrictScalars R
        ((I.map (Ideal.Quotient.mk (Module.annihilator R M))) ^ n • ⊤ :
          Submodule A M) =
      (I ^ n • ⊤ : Submodule R M) := sorry

/-- The Hilbert--Samuel `χ`-function is unchanged after adjoining the annihilator of the
module to the ideal. -/
theorem chi_add_annihilator (I : Ideal R) (n : ℕ) :
    I.hilbertSamuelChi M n =
      (I + Module.annihilator R M).hilbertSamuelChi M n := sorry

/-- The Hilbert--Samuel `χ`-function agrees with that of the image ideal over the canonical
annihilator quotient of the scalar ring. -/
theorem chi_quotientAnnihilator (I : Ideal R) (n : ℕ) :
    let A := R ⧸ Module.annihilator R M
    -- Local instance justification (search instability): the canonical quotient-annihilator action is intentionally selected locally.
    letI : Module A M := Module.quotientAnnihilator
    I.hilbertSamuelChi M n =
      (I.map (Ideal.Quotient.mk (Module.annihilator R M))).hilbertSamuelChi M n := sorry

/-- If adjoining the annihilator makes `I` an ideal of definition, the canonical Hilbert--Samuel
polynomial for `I` represents its `χ`-function eventually. -/
theorem chiPolynomial_spec_of_add_annihilator [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R)
    (hI : (I + Module.annihilator R M).IsIdealOfDefinition) :
    (chiPolynomial I M).EventuallyEqNat
      (fun n ↦ ((I.hilbertSamuelChi M n).toNat : ℚ)) := sorry

/-- Degree-`d` Hilbert--Samuel multiplicity is unchanged when the annihilator of the module is
adjoined to the ideal under the finite-colength hypothesis. -/
theorem multiplicityInDegree_add_annihilator [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R M] (I : Ideal R) (d : ℕ)
    (hI : (I + Module.annihilator R M).IsIdealOfDefinition) :
    multiplicityInDegree I M d =
      multiplicityInDegree (I + Module.annihilator R M) M d := sorry

end Ideal.HilbertSamuel
