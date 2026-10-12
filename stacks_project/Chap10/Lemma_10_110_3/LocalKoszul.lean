/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Bounded.LocalRing
public import ReasLib.Algebra.Homology.ChainComplex.ModuleSingle
public import ReasLib.RingTheory.Sequence.Koszul.Family
import StacksCheckRecall

/-!
# Local Koszul support for Lemma 10.110.3

@stack 00OA
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

@[stacks 00OA "canonical finite-family Koszul linear form"]
#check @koszulLinearForm

@[stacks 00OA "canonical finite-family Koszul complex"]
#check @KoszulComplex.family

@[stacks 00OA "termwise freeness of the canonical finite-family Koszul complex"]
#check @KoszulComplex.family_isTermwiseFree

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (ChainComplex.single₀ (ModuleCat R)) (ModuleCat.of R M)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: a bounded finite free resolution kills residue-field Tor
strictly above the bound. -/
@[stacks 00OA "Tor vanishing above a finite free resolution bound"]
lemma tor_residueField_isZero_of_finiteFreeResolutionLengthLE_lt
    {d n : ℕ}
    (hres : ChainComplex.FiniteFreeResolution.HasLengthLE R (ResidueField R) d)
    (hdn : d < n) :
    Limits.IsZero
      ((((CategoryTheory.Tor (ModuleCat R) n).obj (ModuleCat.of R (ResidueField R))).obj
        (ModuleCat.of R (ResidueField R)))) := sorry

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the local Koszul complex on a finite family `x : Fin n → R`. -/
noncomputable abbrev localKoszulComplexOn {n : ℕ} (x : Fin n → R) :
    ChainComplex (ModuleCat R) ℕ :=
  KoszulComplex.family x

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: every term of the finite-family local Koszul complex is a
free `R`-module. -/
abbrev localKoszulComplexOn_termwiseFree {n : ℕ} (x : Fin n → R) :
    ChainComplex.IsTermwiseFree (localKoszulComplexOn x) :=
  KoszulComplex.family_isTermwiseFree x

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-one Koszul differential followed by the
residue-field degree-zero projection is zero for maximal-ideal coefficients. -/
lemma localKoszulAugmentation_d_comp_zero {n : ℕ} (x : Fin n → maximalIdeal R) :
    ((localKoszulComplexOn (R := R) (fun i ↦ (x i : R))).d 1 0) ≫
      ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap) = 0 := sorry

/-- Helper for Chap10 Lemma 10 110 3: the canonical augmentation from the local Koszul complex on
maximal-ideal lifts to the residue-field single complex. -/
@[stacks 00OA "local Koszul augmentation"]
noncomputable def localKoszulAugmentation {n : ℕ} (x : Fin n → maximalIdeal R) :
    localKoszulComplexOn (R := R) (fun i ↦ (x i : R)) ⟶ moduleSingle[R] (ResidueField R) :=
  (ChainComplex.toSingle₀Equiv
      (localKoszulComplexOn (R := R) (fun i ↦ (x i : R)))
      (ModuleCat.of R (ResidueField R))).symm
    ⟨ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap),
      localKoszulAugmentation_d_comp_zero (R := R) x⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 110 3: the degree-zero component of the local Koszul augmentation is
the residue map after the canonical `⋀^0 ≃ R` identification. -/
@[stacks 00OA "degree-zero component of the local Koszul augmentation"]
theorem localKoszulAugmentation_f_zero {n : ℕ} (x : Fin n → maximalIdeal R) :
    (localKoszulAugmentation (R := R) x).f 0 =
      ModuleCat.ofHom (((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap).comp
        (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap) := sorry

end
