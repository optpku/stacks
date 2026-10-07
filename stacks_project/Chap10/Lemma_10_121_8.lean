module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import ReasLib.RingTheory.LocalRing.Finite
import StacksCheckRecall

/-!
# Norms and orders of vanishing in finite extensions

@stack 02MJ

The local order and determinant primitives are canonical library owners.  This
file keeps only the finite-extension weighted-sum view used by the source.
-/

@[expose] public section

open scoped BigOperators nonZeroDivisors
open IsLocalRing

noncomputable section

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
variable [IsLocalRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable [Module.Finite A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]

-- Local declaration justification (source-local instances): these FractionRing
-- lifts pin the finite-extension tower used by the source statement; they are
-- not canonical global instances for arbitrary fraction-field maps.
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- A module-finite extension of a local domain of dimension at most one has
localizations at maximal ideals of dimension at most one. -/
theorem MaximalSpectrum.krullDimLE_one_localizationAtPrime_of_moduleFinite
    (m : MaximalSpectrum B) :
    Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) := sorry

-- Local declaration justification (source-local notation): `κA` abbreviates
-- the base residue field in the weighted sum and is not a new public object.
local notation "κA" => Ideal.ResidueField (maximalIdeal A)

-- Local declaration justification (source-local instance): the residue-field
-- algebra is selected from the displayed lying-over pair for each `m`.
local instance residueFieldAlgebra_of_moduleFinite (m : MaximalSpectrum B) :
    Algebra κA (Ideal.ResidueField m.asIdeal) :=
  Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) m.asIdeal

/-! A finite extension has only finitely many maximal ideals; this is a
canonical ReasLib owner and is recalled here rather than re-proved. -/

@[stacks 02MJ "semilocality owner"]
#check @MaximalSpectrum.finite_of_moduleFinite

/-- Lemma 10.121.8 (02MJ): let `A → B` be a finite extension of domains with
`A` a Noetherian local domain of dimension one.  For
`y : (FractionRing B)ˣ`, the order of the norm is the residue-degree weighted
sum of the local orders at the maximal ideals of `B`.  The explicit `hdim`
argument records the source's dimension-one hypothesis; the ambient
`Ring.KrullDimLE` instance supplies the canonical upper-bound APIs. -/
@[stacks 02MJ]
-- The finite-index and localized Noetherian/dimension values below are
-- source-facing pins, derived per maximal ideal rather than global instances.
theorem ordFrac_norm_eq_sum_residueFieldDegree_mul_local_ordFrac
    (hdim : ringKrullDim A = 1) (y : (FractionRing B)ˣ) :
    WithZero.log
        (Ring.ordFrac A (Algebra.norm (FractionRing A) (y : FractionRing B))) =
      let _ : Finite (MaximalSpectrum B) :=
        MaximalSpectrum.finite_of_moduleFinite A
      let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
      let _ : IsNoetherianRing B := IsNoetherianRing.of_finite A B
      let _ : ∀ m : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        fun m ↦
          IsLocalization.isNoetherianRing m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal) inferInstance
      let _ : ∀ m : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime m.asIdeal) :=
        fun m ↦ MaximalSpectrum.krullDimLE_one_localizationAtPrime_of_moduleFinite (B := B) m
      ∑ m : MaximalSpectrum B,
        (Module.finrank κA (Ideal.ResidueField m.asIdeal) : ℤ) *
          WithZero.log
            (Ring.ordFrac (Localization.AtPrime m.asIdeal) (y : FractionRing B)) := sorry

end

end
