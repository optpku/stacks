/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Determinant lines under restriction of scalars

A local homomorphism inducing an equivalence on residue fields transports admissible
determinant symbols, and hence determinant lines, across restriction of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u u' v

namespace Module.FiniteLengthDeterminant.Restriction

variable {R' : Type u'} {R : Type u} [CommRing R'] [CommRing R]
variable [IsLocalRing R'] [IsLocalRing R]
variable (f : R' →+* R) [IsLocalHom f]

/-- The residue-field equivalence induced by a bijective residue-field map. -/
noncomputable def residueEquiv
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    IsLocalRing.ResidueField R' ≃+* IsLocalRing.ResidueField R :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.map f) hκ

/-- The forward ring homomorphism of `residueEquiv` is the induced residue-field map. -/
theorem residueEquiv_toRingHom
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    (residueEquiv f hκ).toRingHom = IsLocalRing.ResidueField.map f := rfl

/-- The induced residue-field equivalence and its inverse form an inverse pair of ring maps. -/
instance residueEquiv_toSymmInvPair
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    RingHomInvPair (residueEquiv f hκ).toRingHom (residueEquiv f hκ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (residueEquiv f hκ)

/-- The inverse and forward maps of the induced residue-field equivalence form an inverse pair. -/
instance residueEquiv_symmToInvPair
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) :
    RingHomInvPair (residueEquiv f hκ).symm.toRingHom (residueEquiv f hκ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (residueEquiv f hκ)

private theorem moduleLength_eq
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f)) (M : ModuleCat.{v} R) :
    Module.length R' ((ModuleCat.restrictScalars f).obj M) = Module.length R M := by
  letI : Algebra R' R := f.toAlgebra
  letI : IsScalarTower R' R ((ModuleCat.restrictScalars f).obj M) :=
    ⟨fun r s m ↦ mul_smul (f r) s (m : M)⟩
  have hres : Module.length (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField R) = 1 := by
    rw [Module.length_eq_of_surjective (show Function.Surjective
      (algebraMap (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField R)) from hκ.2)]
    exact Module.length_eq_one _ _
  rw [IsLocalRing.length_restrictScalars R' R _, hres, mul_one]
  change Module.length R (M : Type v) = Module.length R (M : Type v)
  rfl

/-- Finite length is preserved by restriction along a local homomorphism inducing a residue-field
equivalence. -/
theorem isFiniteLength (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    IsFiniteLength R' ((ModuleCat.restrictScalars f).obj M) := by
  apply Module.length_ne_top_iff.mp
  rw [moduleLength_eq f hκ M]
  exact Module.length_ne_top_iff.mpr hM

/-- Restriction along `f` does not change the natural-number length indexing determinant
symbols. -/
theorem length_eq (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    length R' ((ModuleCat.restrictScalars f).obj M) (isFiniteLength f hκ M hM) =
      length R M hM := by
  exact congrArg ENat.toNat (moduleLength_eq f hκ M)

/-- Reindex an admissible determinant sequence after restriction of scalars. -/
def sequence (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    Fin (length R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM)) → (ModuleCat.restrictScalars f).obj M :=
  fun i ↦ s.1 (finCongr (length_eq f hκ M hM) i)

/-- Evaluation of the restricted determinant sequence is the corresponding evaluation of the
original sequence. -/
theorem sequence_apply (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM)
    (i : Fin (length R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM))) :
    sequence f hκ M hM s i = s.1 (finCongr (length_eq f hκ M hM) i) := rfl

-- Lift coefficients of an admissible prefix from the common residue field.
private theorem mem_prefixSpan_restrict
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) {n : ℕ} (e : Fin n → M)
    (he : ∀ i r, r ∈ IsLocalRing.maximalIdeal R → r • e i ∈ prefixSpan R M e i)
    (i : Fin n) {x : M} (hx : x ∈ prefixSpan R M e i) :
    x ∈ prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i := by
  refine (wellFounded_lt.induction (C := fun i : Fin n ↦ ∀ x : M,
    x ∈ prefixSpan R M e i →
      x ∈ prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i) i ?_) x hx
  intro i ih x hx
  have hsmul : ∀ r : R,
      r • x ∈ prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨j, hji, rfl⟩
      intro r
      obtain ⟨a, ha⟩ := (hκ.2.comp (IsLocalRing.residue_surjective (R := R')))
        (IsLocalRing.residue R r)
      change IsLocalRing.residue R (f a) = IsLocalRing.residue R r at ha
      have hb : r - f a ∈ IsLocalRing.maximalIdeal R := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        rw [map_sub, ha, sub_self]
      have hprev := ih j hji _ (he j (r - f a) hb)
      have hle : prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e j ≤
          prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i :=
        Submodule.span_mono (Set.image_mono (fun k (hk : k ∈ Set.Iio j) ↦ by
          change k < j at hk
          change j < i at hji
          exact lt_trans hk hji))
      have hgen : (e j : (ModuleCat.restrictScalars f).obj M) ∈
          prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i :=
        Submodule.subset_span ⟨j, hji, rfl⟩
      have hlift := (prefixSpan R' ((ModuleCat.restrictScalars f).obj M) e i).smul_mem a hgen
      have hsplit : r • e j = f a • e j + (r - f a) • e j := by
        rw [← add_smul, add_sub_cancel]
      rw [hsplit]
      exact Submodule.add_mem _ hlift (hle hprev)
    | zero =>
      intro r
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro r
      rw [smul_add]
      exact Submodule.add_mem _ (ihy r) (ihz r)
    | smul a y hy ihy =>
      intro r
      rw [smul_smul]
      exact ihy (r * a)
  simpa using hsmul 1

/-- A determinant sequence admissible over `R` remains admissible after restriction to `R'`. -/
theorem sequence_isAdmissible
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    IsAdmissible R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM) (sequence f hκ M hM s) := by
  letI : Module R' M := Module.compHom M f
  intro i r hr
  have hm : f r ∈ IsLocalRing.maximalIdeal R := map_nonunit f r hr
  have hx := mem_prefixSpan_restrict f hκ M s.1 s.2
    (finCongr (length_eq f hκ M hM) i) (s.2 _ _ hm)
  have hset : s.1 '' Set.Iio (finCongr (length_eq f hκ M hM) i) =
      sequence f hκ M hM s '' Set.Iio i := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(finCongr (length_eq f hκ M hM)).symm j, ?_, ?_⟩
      · exact hj
      · simp [sequence]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨finCongr (length_eq f hκ M hM) j, hj, rfl⟩
  unfold prefixSpan
  change r • (s.1 (finCongr (length_eq f hκ M hM) i) :
      (ModuleCat.restrictScalars f).obj M) ∈
    Submodule.span R' (sequence f hκ M hM s '' Set.Iio i)
  rw [← hset]
  exact hx

/-- The admissible determinant symbol obtained by restriction of scalars. -/
def symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    Symbol R' ((ModuleCat.restrictScalars f).obj M) (isFiniteLength f hκ M hM) :=
  ⟨sequence f hκ M hM s, sequence_isAdmissible f hκ M hM s⟩

/-- The underlying sequence of a restricted determinant symbol is `sequence`. -/
theorem symbol_coe (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    (symbol f hκ M hM s).1 = sequence f hκ M hM s := rfl

/-- The semilinear map from the free module on `R`-symbols to the restricted determinant line. -/
def freeHom (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Free R M hM →ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  Finsupp.lsum (IsLocalRing.ResidueField R') fun s ↦
    (LinearMap.toSpanSingleton (IsLocalRing.ResidueField R')
      (Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM))
      (Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s))).comp
      (residueEquiv f hκ).symm.toRingHom.toSemilinearMap

/-- The free semilinear map sends a basis symbol to its restricted determinant symbol. -/
theorem freeHom_single
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    freeHom f hκ M hM (Finsupp.single s 1) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := by
  rw [freeHom, Finsupp.lsum_single]
  simp only [LinearMap.comp_apply, RingHom.coe_toSemilinearMap, map_one,
    LinearMap.toSpanSingleton_apply_one]

private theorem prefixSpan_sequence
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM)
    (i : Fin (length R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM))) :
    prefixSpan R' ((ModuleCat.restrictScalars f).obj M) (sequence f hκ M hM s) i =
      prefixSpan R' ((ModuleCat.restrictScalars f).obj M) s.1
        (finCongr (length_eq f hκ M hM) i) := by
  apply congrArg (Submodule.span R')
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨finCongr (length_eq f hκ M hM) j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(finCongr (length_eq f hκ M hM)).symm j, hj, ?_⟩
    simp [sequence]

private theorem mem_prefixSpan_symbol
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM)
    (i : Fin (length R M hM)) {x : M} (hx : x ∈ prefixSpan R M s.1 i) :
    x ∈ prefixSpan R' ((ModuleCat.restrictScalars f).obj M)
      (symbol f hκ M hM s).1
      ((finCongr (length_eq f hκ M hM)).symm i) := by
  letI : Module R' M := Module.compHom M f
  have hx' := mem_prefixSpan_restrict f hκ M s.1 s.2 i hx
  change x ∈ prefixSpan R' ((ModuleCat.restrictScalars f).obj M)
    (sequence f hκ M hM s)
    ((finCongr (length_eq f hκ M hM)).symm i)
  rw [prefixSpan_sequence]
  simpa only [Equiv.apply_symm_apply] using hx'

/-- The free semilinear symbol map sends the determinant-relation submodule into zero. -/
theorem relationSubmodule_le_ker
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant.relationSubmodule R M hM ≤
      LinearMap.ker (freeHom f hκ M hM) := by
  letI : Module R' M := Module.compHom M f
  let c := finCongr (length_eq f hκ M hM)
  have kill : ∀ t, Relation R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM) t →
      (relationSubmodule R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM)).mkQ t = 0 := by
    intro t ht
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ht)
  apply Submodule.span_le.mpr
  intro t ht
  change freeHom f hκ M hM t = 0
  cases ht with
  | zero e a ha =>
    rw [freeHom_single]
    exact kill _ (Relation.zero (symbol f hκ M hM e) (c.symm a)
      (mem_prefixSpan_symbol f hκ M hM e a ha))
  | unitChange e e' a unit x hAway ha hx =>
    obtain ⟨a', ha'⟩ := IsLocalRing.residue_surjective (R := R')
      ((residueEquiv f hκ).symm (IsLocalRing.residue R (unit : R)))
    have hu : IsUnit a' := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit a').mp
      rw [ha']
      intro hz
      have hz' := congrArg (residueEquiv f hκ) hz
      simp only [RingEquiv.apply_symm_apply, map_zero] at hz'
      exact ((IsLocalRing.residue_ne_zero_iff_isUnit (unit : R)).mpr unit.isUnit) hz'
    obtain ⟨v, rfl⟩ := hu
    have hv : IsLocalRing.residue R (f (v : R')) = IsLocalRing.residue R (unit : R) := by
      rw [← IsLocalRing.ResidueField.map_residue, ha']
      exact (residueEquiv f hκ).apply_symm_apply _
    have hdiff : (unit : R) - f (v : R') ∈ IsLocalRing.maximalIdeal R := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, hv, sub_self]
    have hp : prefixSpan R M e'.1 a = prefixSpan R M e.1 a := by
      apply congrArg (Submodule.span R)
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, hAway i (ne_of_lt hi)⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, (hAway i (ne_of_lt hi)).symm⟩
    have htail : ((unit : R) - f (v : R')) • e'.1 a ∈ prefixSpan R M e.1 a := by
      rw [← hp]
      exact e'.2 a _ hdiff
    have htail' := mem_prefixSpan_symbol f hκ M hM e a (Submodule.add_mem _ hx htail)
    rw [map_sub, map_smulₛₗ, freeHom_single, freeHom_single]
    change _ - (residueEquiv f hκ).symm
      (IsLocalRing.residue R (unit : R)) • _ = 0
    rw [← ha']
    change (relationSubmodule R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM)).mkQ _ = 0
    apply kill
    apply Relation.unitChange (symbol f hκ M hM e)
      (symbol f hκ M hM e') (c.symm a) v
      (x + ((unit : R) - f (v : R')) • e'.1 a)
    · intro i hi
      apply hAway
      intro h
      apply hi
      apply c.injective
      exact h.trans (c.apply_symm_apply a).symm
    · change e.1 a = f (v : R') • e'.1 a +
        (x + ((unit : R) - f (v : R')) • e'.1 a)
      rw [ha, sub_smul]
      abel
    · exact htail'
  | swapAdjacent e e' previous next hnext hstrong hswap =>
    rw [map_add, freeHom_single, freeHom_single]
    change (relationSubmodule R' ((ModuleCat.restrictScalars f).obj M)
      (isFiniteLength f hκ M hM)).mkQ _ = 0
    apply kill
    apply Relation.swapAdjacent (symbol f hκ M hM e)
      (symbol f hκ M hM e') (c.symm previous) (c.symm next)
    · exact hnext
    · intro r hr
      exact mem_prefixSpan_symbol f hκ M hM e previous (hstrong (f r) (map_nonunit f r hr))
    · funext i
      change e'.1 (c i) = swapEntries ((ModuleCat.restrictScalars f).obj M)
        (fun j ↦ e.1 (c j)) (c.symm previous) (c.symm next) i
      rw [hswap]
      by_cases hp : c i = previous
      · have hi : i = c.symm previous :=
          c.injective (hp.trans (c.apply_symm_apply previous).symm)
        simp [swapEntries, hi]
      · by_cases hn : c i = next
        · have hi : i = c.symm next :=
            c.injective (hn.trans (c.apply_symm_apply next).symm)
          simp [swapEntries, hi]
          rfl
        · have hi' : i ≠ c.symm previous := by
            intro h
            exact hp (by rw [h, c.apply_symm_apply])
          have hi'' : i ≠ c.symm next := by
            intro h
            exact hn (by rw [h, c.apply_symm_apply])
          simp [swapEntries, hp, hn, hi', hi'']

/-- The semilinear determinant map induced by restriction of scalars. -/
def hom (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant R M hM →ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  (Module.FiniteLengthDeterminant.relationSubmodule R M hM).liftQ
    (freeHom f hκ M hM) (relationSubmodule_le_ker f hκ M hM)

/-- The restriction map carries each determinant symbol to its restricted symbol. -/
theorem hom_symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    hom f hκ M hM (Module.FiniteLengthDeterminant.symbol R M hM s) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := by
  change freeHom f hκ M hM (Finsupp.single s 1) = _
  exact freeHom_single f hκ M hM s

/-- The inverse function of the restriction determinant map is a left inverse. -/
theorem hom_invFun_left
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Function.LeftInverse (Function.invFun (hom f hκ M hM)) (hom f hκ M hM) := sorry

/-- The inverse function of the restriction determinant map is a right inverse. -/
theorem hom_invFun_right
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Function.RightInverse (Function.invFun (hom f hκ M hM)) (hom f hκ M hM) := by
  letI : IsSimpleModule (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) :=
    isSimpleModule_iff_finrank_eq_one.mpr (finrank_eq_one M hM)
  letI : Nontrivial (Module.FiniteLengthDeterminant R M hM) :=
    IsSimpleModule.nontrivial (IsLocalRing.ResidueField R) _
  letI : IsSimpleModule (IsLocalRing.ResidueField R')
      (Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM)) :=
    isSimpleModule_iff_finrank_eq_one.mpr
      (finrank_eq_one _ (isFiniteLength f hκ M hM))
  apply Function.rightInverse_invFun
  apply LinearMap.range_eq_top.mp
  rcases eq_bot_or_eq_top (LinearMap.range (hom f hκ M hM)) with h | h
  · have hz : hom f hκ M hM = 0 := LinearMap.range_eq_bot.mp h
    have hinj := (hom_invFun_left f hκ M hM).injective
    have hsub : Subsingleton (Module.FiniteLengthDeterminant R M hM) :=
      ⟨fun x y ↦ hinj (by rw [hz]; rfl)⟩
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Module.FiniteLengthDeterminant R M hM)
    exact False.elim (hxy (hsub.elim x y))
  · exact h

/-- The canonical semilinear equivalence of determinant lines under restriction of scalars. -/
noncomputable def equiv
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) :
    Module.FiniteLengthDeterminant R M hM ≃ₛₗ[(residueEquiv f hκ).symm.toRingHom]
      Module.FiniteLengthDeterminant R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) :=
  { hom f hκ M hM with
    invFun := Function.invFun (hom f hκ M hM)
    left_inv := hom_invFun_left f hκ M hM
    right_inv := hom_invFun_right f hκ M hM }

/-- The restriction equivalence carries each determinant symbol to its restricted symbol. -/
theorem equiv_symbol (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (M : ModuleCat.{v} R) (hM : IsFiniteLength R M) (s : Symbol R M hM) :
    equiv f hκ M hM (Module.FiniteLengthDeterminant.symbol R M hM s) =
      Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj M)
        (isFiniteLength f hκ M hM) (symbol f hκ M hM s) := by
  exact hom_symbol f hκ M hM s

/-- Restriction of determinant lines is natural in isomorphisms of finite-length modules. -/
theorem equiv_naturality
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    {M N : ModuleCat.{v} R} (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (e : M ≅ N) (x : Module.FiniteLengthDeterminant R M hM) :
    equiv f hκ N hN
        (Module.FiniteLengthDeterminant.mapEquiv hM hN e.toLinearEquiv x) =
      (Module.FiniteLengthDeterminant.mapEquiv
        (isFiniteLength f hκ M hM) (isFiniteLength f hκ N hN)
        ((ModuleCat.restrictScalars f).mapIso e).toLinearEquiv) (equiv f hκ M hM x) := by
  let e' := ((ModuleCat.restrictScalars f).mapIso e).toLinearEquiv
  have hMaps :
      ((hom f hκ N hN).comp (mapHom hM hN e.toLinearEquiv)).comp
          (relationSubmodule R M hM).mkQ =
        ((mapHom (isFiniteLength f hκ M hM)
          (isFiniteLength f hκ N hN) e').comp (hom f hκ M hM)).comp
          (relationSubmodule R M hM).mkQ := by
    apply Finsupp.lhom_ext
    intro s a
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.comp_apply, map_smulₛₗ]
    congr 1
    change hom f hκ N hN
        (mapHom hM hN e.toLinearEquiv (Module.FiniteLengthDeterminant.symbol R M hM s)) =
      mapHom (isFiniteLength f hκ M hM)
        (isFiniteLength f hκ N hN) e'
        (hom f hκ M hM (Module.FiniteLengthDeterminant.symbol R M hM s))
    rw [mapHom_symbol, hom_symbol, hom_symbol, mapHom_symbol]
    congr 1
  exact LinearMap.congr_fun (Submodule.linearMap_qext (relationSubmodule R M hM) hMaps) x

private theorem exactSequence_restrict
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃)
    (e₁ : Symbol R S.X₁ h₁) (e₃ : Symbol R S.X₃ h₃) :
    (fun i ↦ exactSequence S h₁ h₂ h₃ e₁ e₃
      (finCongr (length_eq f hκ S.X₂ h₂) i)) =
      exactSequence (S.map (ModuleCat.restrictScalars f))
        (isFiniteLength f hκ S.X₁ h₁)
        (isFiniteLength f hκ S.X₂ h₂)
        (isFiniteLength f hκ S.X₃ h₃)
        (symbol f hκ S.X₁ h₁ e₁) (symbol f hκ S.X₃ h₃ e₃) := by
  funext i
  have hl₁ := length_eq f hκ S.X₁ h₁
  have hl₃ := length_eq f hκ S.X₃ h₃
  dsimp only [exactSequence, ShortComplex.map]
  simp only [hl₁, hl₃, finCongr_apply_coe]
  split_ifs
  · rfl
  · rfl
  · apply congrArg (Function.invFun (⇑S.g.hom))
    apply congrArg e₃.1
    apply Fin.ext
    simp [hl₃]

private theorem exactSymbol_restrict
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (e₃ : Symbol R S.X₃ h₃) :
    exactSymbol (S.map (ModuleCat.restrictScalars f))
        (isFiniteLength f hκ S.X₁ h₁)
        (isFiniteLength f hκ S.X₂ h₂)
        (isFiniteLength f hκ S.X₃ h₃)
        (hS.map_of_exact (ModuleCat.restrictScalars f))
        (symbol f hκ S.X₁ h₁ e₁) (symbol f hκ S.X₃ h₃ e₃) =
      hom f hκ S.X₂ h₂ (exactSymbol S h₁ h₂ h₃ hS e₁ e₃) := by
  have hz : Module.FiniteLengthDeterminant.symbol R' ((ModuleCat.restrictScalars f).obj S.X₁)
      (isFiniteLength f hκ S.X₁ h₁) (symbol f hκ S.X₁ h₁ e₁) = 0 ↔
      Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁ = 0 := by
    rw [← hom_symbol]
    constructor
    · intro h
      apply (hom_invFun_left f hκ S.X₁ h₁).injective
      rw [h, map_zero]
    · intro h
      rw [h, map_zero]
  by_cases hzero : Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁ = 0
  · have hzero' := hz.mpr hzero
    dsimp only [exactSymbol, ShortComplex.map]
    simp only [dif_pos hzero, dif_pos hzero', map_zero]
  · have hzero' := mt hz.mp hzero
    dsimp only [exactSymbol, ShortComplex.map]
    simp only [dif_neg hzero, dif_neg hzero']
    rw [hom_symbol]
    apply congrArg (Module.FiniteLengthDeterminant.symbol R'
      ((ModuleCat.restrictScalars f).obj S.X₂) (isFiniteLength f hκ S.X₂ h₂))
    apply Subtype.ext
    exact (exactSequence_restrict f hκ S h₁ h₂ h₃ e₁ e₃).symm

private theorem hom_ext_semilinear (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    {K : Type*} [Ring K] {P : Type*} [AddCommGroup P] [Module K P]
    {σ : IsLocalRing.ResidueField R →+* K}
    {g h : Module.FiniteLengthDeterminant R M hM →ₛₗ[σ] P}
    (H : ∀ s : Symbol R M hM,
      g (Module.FiniteLengthDeterminant.symbol R M hM s) =
        h (Module.FiniteLengthDeterminant.symbol R M hM s)) : g = h := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro s a
  change g ((relationSubmodule R M hM).mkQ (Finsupp.single s a)) =
    h ((relationSubmodule R M hM).mkQ (Finsupp.single s a))
  rw [← Finsupp.smul_single_one, map_smul, map_smulₛₗ, map_smulₛₗ]
  exact congrArg (fun z ↦ σ a • z) (H s)

/-- Restriction of determinant lines commutes with the determinant equivalence attached to a
short exact sequence. -/
theorem equiv_exact
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map f))
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (x : Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₃ h₃) :
    Module.FiniteLengthDeterminant.exactEquiv
      (S.map (ModuleCat.restrictScalars f))
      (isFiniteLength f hκ S.X₁ h₁) (isFiniteLength f hκ S.X₂ h₂)
      (isFiniteLength f hκ S.X₃ h₃)
      (hS.map_of_exact (ModuleCat.restrictScalars f))
      (TensorProduct.congr (equiv f hκ S.X₁ h₁) (equiv f hκ S.X₃ h₃) x) =
      equiv f hκ S.X₂ h₂
        (Module.FiniteLengthDeterminant.exactEquiv S h₁ h₂ h₃ hS x) := by
  let T := S.map (ModuleCat.restrictScalars f)
  let h₁' := isFiniteLength f hκ S.X₁ h₁
  let h₂' := isFiniteLength f hκ S.X₂ h₂
  let h₃' := isFiniteLength f hκ S.X₃ h₃
  let hT := hS.map_of_exact (ModuleCat.restrictScalars f)
  have hMaps :
      (exactHom T h₁' h₂' h₃' hT).comp
          (TensorProduct.map (hom f hκ S.X₁ h₁) (hom f hκ S.X₃ h₃)) =
        (hom f hκ S.X₂ h₂).comp (exactHom S h₁ h₂ h₃ hS) := by
    apply TensorProduct.ext
    apply hom_ext_semilinear S.X₁ h₁
    intro e₁
    apply hom_ext_semilinear S.X₃ h₃
    intro e₃
    change exactHom T h₁' h₂' h₃' hT
        (hom f hκ S.X₁ h₁ (Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁) ⊗ₜ
          hom f hκ S.X₃ h₃ (Module.FiniteLengthDeterminant.symbol R S.X₃ h₃ e₃)) =
      hom f hκ S.X₂ h₂ (exactHom S h₁ h₂ h₃ hS
        (Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁ ⊗ₜ
          Module.FiniteLengthDeterminant.symbol R S.X₃ h₃ e₃))
    rw [hom_symbol, hom_symbol, exactHom_tmul_symbol S h₁ h₂ h₃ hS]
    exact (exactHom_tmul_symbol T h₁' h₂' h₃' hT
      (symbol f hκ S.X₁ h₁ e₁) (symbol f hκ S.X₃ h₃ e₃)).trans
      (exactSymbol_restrict f hκ S h₁ h₂ h₃ hS e₁ e₃)
  exact LinearMap.congr_fun hMaps x

end Module.FiniteLengthDeterminant.Restriction
