/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Complex.Functors

@[expose] public section

/-!
# The Stupid (Brutal Truncation) Filtration on a Cochain Complex

For a cochain complex `K` in an abelian category, the *stupid filtration* is the decreasing
filtration whose `p`-th stage is the "brutal" (stupid) truncation `σ≥p(K^•)`: the subcomplex
agreeing with `K` in degrees `≥ p` and vanishing in degrees `< p`.

## Main definitions

* `CochainComplex.stupidFiltrationSubobject K p n` — the degreewise subobject of `K.X n`
  cutting out the stupid filtration: `⊤` when `p ≤ n`, and `⊥` otherwise.
* `CochainComplex.stupidFiltration K` — the resulting filtered cochain complex
  `K.stupidFiltration : FilteredComplex 𝒜`.

## Main results

* `CochainComplex.stupidFiltration_hasFiniteFiltrations` — the stupid filtration has finite
  filtrations in every degree.
* `CochainComplex.StupidFiltration.stageIso` — the `p`-th stage of the stupid filtration is
isomorphic to Mathlib's brutal truncation `K.stupidTrunc (embeddingUpIntGE p)`.

## Implementation notes

Stage evaluation, its natural inclusions, and termwise finite filtrations belong to the neutral
`CategoryTheory.Filtration.Complex` layer.  This file only owns the brutal-truncation-specific
construction and its comparison with Mathlib's `stupidTrunc`.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex

noncomputable section

universe v u

namespace CategoryTheory

namespace CochainComplex

section Filtrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The degreewise subobject defining the stupid filtration `F^p(K^n) = σ≥p(K^n)`. -/
def stupidFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if p ≤ n then ⊤ else ⊥

theorem stupidFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    stupidFiltrationSubobject K q n ≤ stupidFiltrationSubobject K p n := by
  by_cases hqn : q ≤ n
  · have hpn : p ≤ n := le_trans hpq hqn
    simp [stupidFiltrationSubobject, hqn, hpn]
  · simp [stupidFiltrationSubobject, hqn]

theorem stupidFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    stupidFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (stupidFiltrationSubobject K p j) := by
  by_cases hpi : p ≤ i
  · by_cases hij : j = i + 1
    · have hpj : p ≤ j := by omega
      simp [stupidFiltrationSubobject, hpi, hpj, Subobject.pullback_top]
    · apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      have hd : K.d i j = 0 := by
        have hshape : ¬ (ComplexShape.up ℤ).Rel i j := by
          simpa [ComplexShape.up, eq_comm] using hij
        exact K.shape i j hshape
      rw [hd, comp_zero]
      exact Subobject.factors_zero
  · simp [stupidFiltrationSubobject, hpi]

/-- The filtered complex with stages `F^p(K^•) = σ≥p(K^•)`. -/
def stupidFiltration (K : CochainComplex 𝒜 ℤ) : FilteredComplex 𝒜 where
  X n :=
    { obj := K.X n
      filtration :=
        { toFun := fun p ↦ stupidFiltrationSubobject K p n
          monotone' := fun _ _ hpq ↦ stupidFiltration_decreasing K hpq } }
  d i j :=
    { hom := K.d i j
      preserves := fun p ↦
        (pullback_factors_iff (K.d i j) (stupidFiltrationSubobject K p j)
          (stupidFiltrationSubobject K p i).arrow).1 <|
          (Subobject.factors_iff _ _).2
            ⟨Subobject.ofLE _ _ (stupidFiltration_d_preserves K p i j),
              Subobject.ofLE_arrow (stupidFiltration_d_preserves K p i j)⟩ }
  shape := fun i j hij ↦ FilteredObject.forget.map_injective (K.shape i j hij)
  d_comp_d' := fun i j k hij hjk ↦
    FilteredObject.forget.map_injective (K.d_comp_d' i j k hij hjk)

/-- The stupid filtration has finite filtrations in every degree. -/
theorem stupidFiltration_hasFiniteFiltrations (K : CochainComplex 𝒜 ℤ) :
    (stupidFiltration K).HasFiniteFiltrations := by
  intro n
  refine ⟨n, n + 1, ?_, ?_⟩
  · change stupidFiltrationSubobject K n n = ⊤
    simp [stupidFiltrationSubobject]
  · change stupidFiltrationSubobject K (n + 1) n = ⊥
    simp [stupidFiltrationSubobject]

namespace StupidFiltration

/-- At an active degree, the corresponding stage of the stupid filtration is canonically
identified with the original term. -/
noncomputable def stageActiveIso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    ((K.stupidFiltration).stage p).X n ≅ K.X n := by
  change (stupidFiltrationSubobject K p n : 𝒜) ≅ K.X n
  rw [stupidFiltrationSubobject, if_pos hpn, Subobject.top_eq_id]
  exact Subobject.underlyingIso (𝟙 (K.X n))

/-- The forward map of `stageActiveIso` is the canonical inclusion of the filtration stage. -/
theorem stageActiveIso_hom
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (stageActiveIso K p n hpn).hom =
      ((K.stupidFiltration).stageInclusion p).f n := sorry

/-- The inverse active-stage identification is a left inverse to the stage inclusion. -/
theorem stageActiveIso_inv_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (stageActiveIso K p n hpn).inv ≫
      ((K.stupidFiltration).stageInclusion p).f n =
        𝟙 (K.X n) := sorry

/-- A stupid-filtration stage vanishes below its cutoff. -/
theorem termIsZero_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hnp : n < p) :
    IsZero (((K.stupidFiltration).stage p).X n) := by
  change IsZero ((stupidFiltrationSubobject K p n : 𝒜))
  rw [stupidFiltrationSubobject, if_neg (not_le_of_gt hnp)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

end StupidFiltration

namespace StupidTrunc

/-- The natural-number index selected by `embeddingUpIntGE` represents a retained degree. -/
theorem toNatSub_eq
    (p n : ℤ) (hpn : p ≤ n) :
    (embeddingUpIntGE p).f (Int.toNat (n - p)) = n := by
  rw [ComplexShape.embeddingUpIntGE_f]
  omega

/-- At a retained degree, Mathlib's brutal truncation is canonically identified with the
original term. -/
noncomputable def activeIso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hpn : p ≤ n) :
    (K.stupidTrunc (embeddingUpIntGE p)).X n ≅ K.X n :=
  K.stupidTruncXIso (embeddingUpIntGE p) (toNatSub_eq p n hpn)

/-- A brutal truncation vanishes below its cutoff. -/
theorem termIsZero_of_lt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hnp : n < p) :
    IsZero ((K.stupidTrunc (embeddingUpIntGE p)).X n) := by
  refine K.isZero_stupidTrunc_X (embeddingUpIntGE p) n ?_
  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hnp

/-- On retained degrees, the differential of a brutal truncation is the original
differential under `activeIso`. -/
theorem d_viaActiveIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ}
    (hpi : p ≤ i) (hpj : p ≤ j) :
    (StupidTrunc.activeIso K p i hpi).inv ≫
      (K.stupidTrunc (embeddingUpIntGE p)).d i j ≫
      (StupidTrunc.activeIso K p j hpj).hom =
        K.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) := embeddingUpIntGE p
  let i₀ : ℕ := Int.toNat (i - p)
  let j₀ : ℕ := Int.toNat (j - p)
  have hi₀ : e.f i₀ = i := toNatSub_eq p i hpi
  have hj₀ : e.f j₀ = j := toNatSub_eq p j hpj
  change (StupidTrunc.activeIso K p i hpi).inv ≫
      ((K.restriction e).extend e).d i j ≫
      (StupidTrunc.activeIso K p j hpj).hom =
        K.d i j
  rw [HomologicalComplex.extend_d_eq (K := K.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := K) (e := e) hi₀ hj₀]
  simp [StupidTrunc.activeIso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso, e, i₀, j₀]

end StupidTrunc

namespace StupidFiltration

/-- The differential on a filtration stage commutes with its inclusion into the original
complex. -/
theorem d_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    ((K.stupidFiltration).stage p).d i j ≫
      ((K.stupidFiltration).stageInclusion p).f j =
        ((K.stupidFiltration).stageInclusion p).f i ≫ K.d i j := by
  change FilteredObject.Hom.stageMap ((K.stupidFiltration).d i j) p ≫
      (FilteredObject.Stage.toForget p).app ((K.stupidFiltration).X j) =
    (FilteredObject.Stage.toForget p).app ((K.stupidFiltration).X i) ≫
      ((K.stupidFiltration).d i j).hom
  exact (FilteredObject.Stage.toForget p).naturality ((K.stupidFiltration).d i j)

/-- On active degrees, the differential of a stupid-filtration stage is the original
differential under `stageActiveIso`. -/
theorem d_viaActiveIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ}
    (hpi : p ≤ i) (hpj : p ≤ j) (_ : (ComplexShape.up ℤ).Rel i j) :
    (StupidFiltration.stageActiveIso K p i hpi).inv ≫
      ((K.stupidFiltration).stage p).d i j ≫
      (StupidFiltration.stageActiveIso K p j hpj).hom =
        K.d i j := by
  rw [StupidFiltration.stageActiveIso_hom K p j hpj]
  change (StupidFiltration.stageActiveIso K p i hpi).inv ≫
      (((K.stupidFiltration).stage p).d i j ≫ ((K.stupidFiltration).stageInclusion p).f j) =
    K.d i j
  rw [d_comp_inclusion K p i j]
  change (StupidFiltration.stageActiveIso K p i hpi).inv ≫
      (((K.stupidFiltration).stageInclusion p).f i ≫ K.d i j) =
    K.d i j
  rw [← Category.assoc]
  erw [StupidFiltration.stageActiveIso_inv_comp_inclusion K p i hpi]
  erw [Category.id_comp]

/-- The `p`-th stage of the stupid filtration is the brutal truncation `σ≥p(K^•)`. -/
noncomputable def stageIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.stupidFiltration).stage p ≅ K.stupidTrunc (embeddingUpIntGE p) :=
  let e :
      ∀ n : ℤ, ((K.stupidFiltration).stage p).X n ≅
        (K.stupidTrunc (embeddingUpIntGE p)).X n := fun n ↦
    if hpn : p ≤ n then
      stageActiveIso K p n hpn ≪≫
        (StupidTrunc.activeIso K p n hpn).symm
    else
      let hnp : n < p := lt_of_not_ge hpn
      (termIsZero_of_lt K p n hnp).isoZero ≪≫
        (StupidTrunc.termIsZero_of_lt K p n hnp).isoZero.symm
  HomologicalComplex.Hom.isoOfComponents e (by
    intro i j hij
    by_cases hpi : p ≤ i
    · have hpj : p ≤ j := by
        have hij' : j = i + 1 := by
          simpa [ComplexShape.up, eq_comm] using hij
        omega
      let eStageI : ((K.stupidFiltration).stage p).X i ≅ K.X i :=
        stageActiveIso K p i hpi
      let eStageJ : ((K.stupidFiltration).stage p).X j ≅ K.X j :=
        stageActiveIso K p j hpj
      let eTruncI : (K.stupidTrunc (embeddingUpIntGE p)).X i ≅ K.X i :=
        StupidTrunc.activeIso K p i hpi
      let eTruncJ : (K.stupidTrunc (embeddingUpIntGE p)).X j ≅ K.X j :=
        StupidTrunc.activeIso K p j hpj
      have he_i : (e i).hom = eStageI.hom ≫ eTruncI.inv := by
        simp [e, hpi, eStageI, eTruncI]
      have he_j : (e j).hom = eStageJ.hom ≫ eTruncJ.inv := by
        simp [e, hpj, eStageJ, eTruncJ]
      apply (cancel_mono eTruncJ.hom).1
      rw [he_i, he_j]
      simp_rw [Category.assoc]
      calc
        eStageI.hom ≫ eTruncI.inv ≫
            (K.stupidTrunc (embeddingUpIntGE p)).d i j ≫ eTruncJ.hom
          = eStageI.hom ≫ K.d i j := by
              rw [StupidTrunc.d_viaActiveIso K p hpi hpj]
        _ = eStageI.hom ≫
            (eStageI.inv ≫ ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom) := by
              rw [d_viaActiveIso K p hpi hpj hij]
        _ = ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom := by
              simp
        _ = ((K.stupidFiltration).stage p).d i j ≫ eStageJ.hom ≫ eTruncJ.inv ≫ eTruncJ.hom := by
              simp
    · exact (termIsZero_of_lt K p i (lt_of_not_ge hpi)).eq_of_src _ _)

end StupidFiltration

end Filtrations

end CochainComplex

end CategoryTheory
