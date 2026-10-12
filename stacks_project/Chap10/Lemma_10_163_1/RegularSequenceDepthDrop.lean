/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_163_1.ClosedFiberDepthZero
public import ReasLib.LinearAlgebra.LinearMap.Ladder
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
public import ReasLib.RingTheory.Depth.RegularSequence
public import ReasLib.RingTheory.Depth.SupportDim
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Sequence.Regularity

@[expose] public section

open RingTheory Sequence Ideal IsLocalRing
open Ideal.Quotient.Map
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct Pointwise Ideal.Fiber.Quotient Algebra.TensorProduct.Right

universe u v w x uA uP

section

variable {R : Type u} {S : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] N

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite R M] [Module.Finite S N] in
/-- Helper for Lemma 10.163.1: a source nonzerodivisor stays regular after tensoring with the flat
target module `N`, viewed as an `S`-linear endomorphism of `N ⊗[R] M`. -/
lemma source_regular_on_tensor {x : R} (hreg : IsSMulRegular M x) :
    IsSMulRegular (N ⊗[R] M) (algebraMap R S x) := by
  have hTensor : IsSMulRegular (N ⊗[R] M) x :=
    IsSMulRegular.lTensor (R := R) (M := N) hreg
  -- Proof comment: the `S`-action by `algebraMap R S x` agrees with the restricted `R`-action by
  -- `x`, so the flat-tensor regularity statement applies verbatim.
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  exact hTensor.right_eq_zero_of_smul <| by
    simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hz

/-- Helper for Lemma 10.163.1: quotienting `N ⊗[R] M` by the source element `x` acting through
`R → S` agrees with tensoring `N` against the quotient `M / xM`. -/
noncomputable def tensor_quotient_by_source_element (x : R) :
    QuotSMulTop (algebraMap R S x) (N ⊗[R] M) ≃ₗ[S] N ⊗[R] QuotSMulTop x M := by
  let e₀ :
      ((S ⊗[R] M) ⊗[S] N) ≃ₗ[S] (N ⊗[R] M) :=
    (TensorProduct.comm S (S ⊗[R] M) N).trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M
  let e₁ :
      QuotSMulTop (algebraMap R S x) (N ⊗[R] M) ≃ₗ[S]
        QuotSMulTop (algebraMap R S x) ((S ⊗[R] M) ⊗[S] N) :=
    QuotSMulTop.congr (algebraMap R S x) e₀.symm
  let e₂ :
      QuotSMulTop (algebraMap R S x) ((S ⊗[R] M) ⊗[S] N) ≃ₗ[S]
        QuotSMulTop (algebraMap R S x) (S ⊗[R] M) ⊗[S] N :=
    (QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop
      (r := algebraMap R S x) (M' := S ⊗[R] M) (M := N)).symm
  let e₃ :
      QuotSMulTop (algebraMap R S x) (S ⊗[R] M) ⊗[S] N ≃ₗ[S]
        (S ⊗[R] QuotSMulTop x M) ⊗[S] N :=
    (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
      (R := R) (r := x) (M := M) S).rTensor N
  let e₄ :
      (S ⊗[R] QuotSMulTop x M) ⊗[S] N ≃ₗ[S] N ⊗[R] QuotSMulTop x M :=
    (TensorProduct.comm S (S ⊗[R] QuotSMulTop x M) N).trans <|
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N (QuotSMulTop x M)
  -- Proof comment: rewrite the tensor product through `S ⊗[R] M`, commute quotienting past the
  -- outer `S`-tensor factor, then use the standard base-change cancellation again on `M / xM`.
  exact e₁.trans (e₂.trans (e₃.trans e₄))

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [Module R N] [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R N] in
/-- Helper for Lemma 10.163.1: regularity of the lifted element on the canonical closed-fiber
module makes multiplication by its quotient class injective on the quotient model
`N ⧸ (𝔪S • ⊤)`. -/
lemma quotient_smul_injective_of_closed_fiber_regular {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    Function.Injective
      (LinearMap.lsmul (S ⧸ 𝔪S) (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) := by
  let e := Ideal.Fiber.Quotient.maximalTensorModuleEquiv (R := R) (S := S)
    (maximalIdeal R) N
  intro x y hxy
  -- Proof comment: conjugate quotient multiplication through the closed-fiber owner equivalence,
  -- use regularity on `ClosedFiberModule`, and then pull equality back through the equivalence.
  apply e.symm.injective
  apply hreg
  apply e.injective
  calc
    e ((algebraMap S ClosedFiber f) • e.symm x) =
        (Ideal.Quotient.mk 𝔪S f) • e (e.symm x) := by
          simpa [e] using
            Ideal.Fiber.Quotient.maximalTensorModuleEquiv_smul_algebraMap
              (R := R) (S := S) (maximalIdeal R) N f (e.symm x)
    _ = (LinearMap.lsmul (S ⧸ 𝔪S)
          (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) x := by
          simp
    _ = (LinearMap.lsmul (S ⧸ 𝔪S)
          (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)) y := hxy
    _ = (Ideal.Quotient.mk 𝔪S f) • e (e.symm y) := by
          simp
    _ = e ((algebraMap S ClosedFiber f) • e.symm y) := by
          symm
          simpa [e] using
            Ideal.Fiber.Quotient.maximalTensorModuleEquiv_smul_algebraMap
              (R := R) (S := S) (maximalIdeal R) N f (e.symm y)

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [IsNoetherianRing S]
  [Module.Finite S N] [Module.Flat R N] in
/-- Helper for Lemma 10.163.1: closed-fiber regularity gives the exact injectivity hypothesis on
`N / maximalIdeal R • N` needed by Lemma `10.99.1` for multiplication by a lift `f : S`. -/
lemma quotient_multiplication_injective_of_closed_fiber_regular {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    Function.Injective
      (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) := by
  let e := smulTopQuotientEquiv (R := R) (S := S) (M := N) (maximalIdeal R)
  let v :
      (N ⧸ (𝔪S • (⊤ : Submodule S N))) →ₗ[R]
        N ⧸ (𝔪S • (⊤ : Submodule S N)) :=
    (LinearMap.lsmul (S ⧸ 𝔪S)
      (N ⧸ (𝔪S • (⊤ : Submodule S N))) (Ideal.Quotient.mk 𝔪S f)).restrictScalars R
  have hcompare :
      (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)).comp
          e.toLinearMap =
        e.toLinearMap.comp v := by
    -- Proof comment: compare the two quotient maps on representatives and use the dedicated
    -- naturality lemma instead of unfolding the entire quotient-owner square globally.
    apply LinearMap.ext
    intro q
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (𝔪S • (⊤ : Submodule S N)) q
    simpa [e, v, LinearMap.comp_apply] using
      smulTopQuotientEquiv_lsmul_mk (R := R) (S := S) (M := N)
        (maximalIdeal R) f n
  exact
    LinearMap.injective_of_ladder_linearEquiv (R := R) hcompare
      (quotient_smul_injective_of_closed_fiber_regular
        (R := R) (S := S) (N := N) hreg)

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.163.1: a lift of a closed-fiber regular element is regular on `N`, and
the quotient `N / fN` remains flat over `R`. -/
lemma lift_closed_fiber_regular_element {f : S}
    (hreg : IsSMulRegular ClosedFiberModule (algebraMap S ClosedFiber f)) :
    IsSMulRegular N f ∧ Module.Flat R (QuotSMulTop f N) := by
  let u : N →ₗ[S] N := LinearMap.lsmul S N f
  have hmod :
      Function.Injective
        (((LinearMap.lsmul S N f).restrictScalars R).quotientMapByIdeal (maximalIdeal R)) :=
    quotient_multiplication_injective_of_closed_fiber_regular
      (R := R) (S := S) (N := N) hreg
  have hu :
      Function.Injective (u.restrictScalars R) :=
    LinearMap.injective_of_mod_maximalIdeal_injective
      (R := R) (S := S) (M := N) (N := N) (u.restrictScalars R) hmod
  have hflat_range :
      Module.Flat R (N ⧸ LinearMap.range (u.restrictScalars R)) :=
    LinearMap.flat_quotient_range_of_mod_maximalIdeal_injective
      (R := R) (S := S) (M := N) (N := N) (u.restrictScalars R) hmod
  have hrange :
      LinearMap.range u = f • (⊤ : Submodule S N) := by
    ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact Submodule.smul_mem_pointwise_smul m f (⊤ : Submodule S N) trivial
    · intro hn
      rcases (Submodule.mem_smul_pointwise_iff_exists n f (⊤ : Submodule S N)).1 hn with
        ⟨m, -, hm⟩
      exact ⟨m, by simpa [u] using hm⟩
  refine ⟨?_, ?_⟩
  · -- Proof comment: injectivity of the multiplication map is exactly scalar-regularity of `f`.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro n hn
    exact hu <| by simpa [u] using hn
  · -- Proof comment: the quotient by the range of multiplication by `f` is definitionally the
    -- quotient `QuotSMulTop f N`.
    have hflat_smul :
        Module.Flat R (N ⧸ (f • (⊤ : Submodule S N)).restrictScalars R) := by
      have hflat_range' := hflat_range
      rw [LinearMap.range_restrictScalars, hrange] at hflat_range'
      exact hflat_range'
    let eRestrict :
        (N ⧸ (f • (⊤ : Submodule S N)).restrictScalars R) ≃ₗ[R]
          N ⧸ (f • (⊤ : Submodule S N)) :=
      Submodule.Quotient.restrictScalarsEquiv R
        (f • (⊤ : Submodule S N))
    letI : Module.Flat R
        (N ⧸ (f • (⊤ : Submodule S N)).restrictScalars R) := hflat_smul
    have hflat_target : Module.Flat R
        (N ⧸ (f • (⊤ : Submodule S N))) :=
      Module.Flat.of_linearEquiv eRestrict.symm
    simpa [QuotSMulTop] using hflat_target

/-- Helper for Lemma 10.163.1: a nonzero finite module over a Noetherian local ring has finite
depth, so the remaining proof may induct on an ordinary natural number. -/
private theorem exists_nat_moduleDepth_of_nontrivial_finite_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    ∃ n : ℕ, moduleDepth A P = n := by
  -- Proof comment: over a local ring, Nakayama rules out `𝔪 P = P` for a nonzero finite module,
  -- so the depth cannot be `⊤`.
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))
  have hfiniteDepth : moduleDepth A P < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := A) (I := maximalIdeal A) (M := P) hsmul
  rcases ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth) with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

/-- Helper for Lemma 10.163.1: if the depth is represented by a natural number, then the module is
nontrivial. -/
private theorem nontrivial_of_moduleDepth_eq_nat_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    {n : ℕ} (hdepth : moduleDepth A P = n) :
    Nontrivial P := by
  -- Proof comment: a subsingleton module has infinite depth, so a finite natural depth excludes
  -- the zero-module branch.
  by_contra hP
  letI : Subsingleton P := not_nontrivial_iff_subsingleton.mp hP
  have htop : moduleDepth A P = ⊤ :=
    moduleDepth_eq_top_of_subsingleton (R := A) (M := P)
  have hnat_top : (n : ℕ∞) = ⊤ := by
    simpa [hdepth] using htop
  have hne_top : (n : ℕ∞) ≠ ⊤ := ENat.coe_ne_top (a := n)
  exact hne_top hnat_top

/-- Helper for Lemma 10.163.1: a maximal-ideal nonzerodivisor gives positive depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P]
    {x : A} (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular P x) :
    (1 : ℕ∞) ≤ moduleDepth A P := by
  letI : Nontrivial (QuotSMulTop x P) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := A) (L := P) hx
  have hnil : IsRegular (R := A) (M := QuotSMulTop x P) [] := by
    simpa using (IsRegular.nil A (QuotSMulTop x P))
  have hsingleton_reg : IsRegular P [x] :=
    IsRegular.cons hreg hnil
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal A := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    by
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))
  -- Proof comment: the singleton regular sequence `[x]` contributes length `1` to the depth
  -- supremum.
  rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Helper for Lemma 10.163.1: the maximal ideal of a Noetherian local ring cannot generate a
nonzero finite module, even in split universes. -/
private lemma maximalIdeal_smul_top_ne_top_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ := by
  -- Proof comment: this is Nakayama's lemma in the Jacobson-ideal form for the maximal ideal.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A P)))

/-- Helper for Lemma 10.163.1: for split universes, depth zero is equivalent to the absence of a
maximal-ideal regular element. -/
private lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] :
    moduleDepth A P = 0 ↔ ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular P x := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := P)
  rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    -- Proof comment: a regular element in the maximal ideal contributes a regular sequence of
    -- length one, contradicting depth zero.
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal P
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((RingTheory.Sequence.isWeaklyRegular_singleton_iff P x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal A := hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular P x :=
            ((RingTheory.Sequence.isRegular_cons_iff P x xs).1 hreg).1
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.163.1: positive finite depth produces a maximal-ideal nonzerodivisor in
split universes. -/
private lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P]
    (hdepth : moduleDepth A P ≠ 0) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular P x := by
  -- Proof comment: contrapose the split-universe zero-depth criterion from the previous helper.
  by_contra hno
  exact hdepth
    ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry (A := A) (P := P)).2 hno)

/-- Helper for Lemma 10.163.1: in split universes, quotienting by a maximal-ideal nonzerodivisor
lowers local depth by at most one. -/
private lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal_univ
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Nontrivial P] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular P x) :
    moduleDepth A (QuotSMulTop x P) ≤ moduleDepth A P - 1 := by
  letI : Nontrivial (QuotSMulTop x P) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := A) (L := P) hx
  -- Proof comment: rewrite both depths as suprema of maximal-ideal regular-sequence lengths and
  -- prepend the regular element `x` to any regular sequence on the quotient.
  have hquot_smul :
      maximalIdeal A • (⊤ : Submodule A (QuotSMulTop x P)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := QuotSMulTop x P)
  have hmodule_smul :
      maximalIdeal A • (⊤ : Submodule A P) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (P := P)
  have hfiniteDepth : moduleDepth A P < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := A) (I := maximalIdeal A) (M := P) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth A P = n := by
    simpa using hn.symm
  rw [show moduleDepth A (QuotSMulTop x P) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal A) (QuotSMulTop x P)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) (QuotSMulTop x P)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : IsRegular P ([x] ++ ys) := by
    have hfull : IsRegular P (x :: ys) := by
      exact IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
    · exact hx
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([x] ++ ys).length : ℕ∞) ≤ moduleDepth A P) := by
    rw [show moduleDepth A P = sSup (Ideal.regularSequenceLengths (maximalIdeal A) P) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) P hmodule_smul]
    refine le_sSup ?_
    exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([x] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

end
