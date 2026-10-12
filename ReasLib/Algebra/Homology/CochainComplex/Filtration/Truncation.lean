/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Transition

@[expose] public section

/-!
# The Truncation (Canonical `τ≤`) Filtration on a Cochain Complex

@stack 015X

For a cochain complex `K` in an abelian category, the *truncation filtration* is the decreasing
filtration whose `p`-th stage is the canonical truncation `τ_{≤ -p}(K^•)`: the subcomplex
agreeing with `K` in degrees `< -p`, the cycles object at degree `-p`, and vanishing above.

## Main definitions

* `CochainComplex.truncationFiltrationSubobject K p n` — the degreewise subobject of `K.X n`
  cutting out the truncation filtration.
* `CochainComplex.truncationFiltration K` — the resulting filtered cochain complex
  `K.truncationFiltration : FilteredComplex 𝒜`.

## Main results

* `CochainComplex.TruncationFiltration.stageIso` — the chosen comparison from the
  `p`-th truncation-filtration stage to Mathlib's canonical truncation `K.truncLE (-p)`.
* `CochainComplex.TruncationFiltration.stageIso_hom_comp_inclusion` — its compatibility
  with the canonical inclusions into `K^•`.

## Implementation notes

Stage evaluation, stage comparisons, natural inclusions, and termwise finite filtrations come
directly from the neutral `CategoryTheory.Filtration.Complex` layer. This file only owns the
canonical-truncation filtration and its comparison with Mathlib's `truncLE`.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CochainComplex

noncomputable section

universe u v

namespace CategoryTheory

namespace CochainComplex

section Filtrations

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The degreewise subobject defining the truncation filtration
`F^p(K^n) = τ_{\le -p}(K^n)`. -/
def truncationFiltrationSubobject (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    Subobject (K.X n) :=
  if n < -p then
    ⊤
  else if n = -p then
    kernelSubobject (K.d n (n + 1))
  else
    ⊥

/-- The truncation filtration is decreasing in the filtration index. -/
theorem truncationFiltration_decreasing (K : CochainComplex 𝒜 ℤ) {p q n : ℤ}
    (hpq : p ≤ q) :
    truncationFiltrationSubobject K q n ≤ truncationFiltrationSubobject K p n := by
  by_cases hqn : n < -q
  · have hpn : n < -p := lt_of_lt_of_le hqn (by simpa using neg_le_neg hpq)
    simp [truncationFiltrationSubobject, hqn, hpn]
  · by_cases heqn : n = -q
    · by_cases hpq_eq : p = q
      · subst hpq_eq
        simp [truncationFiltrationSubobject, hqn, heqn]
      · have hpn : n < -p := by
          omega
        have hpq_lt : p < q := lt_of_le_of_ne hpq hpq_eq
        simp [truncationFiltrationSubobject, heqn, hpn, hpq_lt]
    · simp [truncationFiltrationSubobject, hqn, heqn]

/-- The differential preserves the truncation filtration. -/
theorem truncationFiltration_d_preserves (K : CochainComplex 𝒜 ℤ) (p i j : ℤ) :
    truncationFiltrationSubobject K p i ≤
      (Subobject.pullback (K.d i j)).obj (truncationFiltrationSubobject K p j) := by
  by_cases hi_lt : i < -p
  · by_cases hij : j = i + 1
    · subst hij
      by_cases hj_lt : i + 1 < -p
      · rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_pos hj_lt, Subobject.pullback_top]
      · have hj_eq : i + 1 = -p := by omega
        rw [truncationFiltrationSubobject, if_pos hi_lt, truncationFiltrationSubobject,
          if_neg hj_lt, if_pos hj_eq]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact kernelSubobject_factors _ _ (by
          simpa using K.d_comp_d i (i + 1) (i + 2))
    · have hd : K.d i j = 0 := by
        have hshape : ¬ (ComplexShape.up ℤ).Rel i j := by
          simpa [ComplexShape.up, eq_comm] using hij
        apply K.shape
        exact hshape
      rw [truncationFiltrationSubobject, if_pos hi_lt]
      apply Subobject.le_of_factors
      rw [pullback_factors_iff]
      simpa [hd] using
        (Subobject.factors_zero :
          (truncationFiltrationSubobject K p j).Factors
            (0 : ((⊤ : Subobject (K.X i)) : 𝒜) ⟶ K.X j))
  · by_cases hi_eq : i = -p
    · subst i
      by_cases hij : j = -p + 1
      · subst j
        rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl,
          truncationFiltrationSubobject]
        have hj_not_lt : ¬ -p + 1 < -p := by omega
        have hj_ne : ¬ -p + 1 = -p := by omega
        rw [if_neg hj_not_lt, if_neg hj_ne]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        exact (Subobject.bot_factors_iff_zero _).2 (by
          simpa using (kernelSubobject_arrow_comp (f := K.d (-p) (-p + 1))))
      · have hd : K.d (-p) j = 0 := by
          have hshape : ¬ (ComplexShape.up ℤ).Rel (-p) j := by
            simpa [ComplexShape.up, eq_comm] using hij
          apply K.shape
          exact hshape
        rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl]
        apply Subobject.le_of_factors
        rw [pullback_factors_iff]
        simpa [hd] using
          (Subobject.factors_zero :
            (truncationFiltrationSubobject K p j).Factors
              (0 : ((kernelSubobject (K.d (-p) (-p + 1)) : Subobject (K.X (-p))) : 𝒜) ⟶
                K.X j))
    · rw [truncationFiltrationSubobject, if_neg hi_lt, if_neg hi_eq]
      exact bot_le

/-- The truncation filtration `F^p(K^•) = τ_{\le -p}(K^•)` on a cochain complex. -/
def truncationFiltration (K : CochainComplex 𝒜 ℤ) : FilteredComplex 𝒜 where
  X n :=
    { obj := K.X n
      filtration :=
        { toFun := fun p ↦ truncationFiltrationSubobject K p n
          monotone' := fun _ _ hpq ↦ truncationFiltration_decreasing K hpq } }
  d i j :=
    { hom := K.d i j
      preserves := fun p ↦
        (pullback_factors_iff (K.d i j) (truncationFiltrationSubobject K p j)
          (truncationFiltrationSubobject K p i).arrow).1 <|
          (Subobject.factors_iff _ _).2
            ⟨Subobject.ofLE _ _ (truncationFiltration_d_preserves K p i j),
              Subobject.ofLE_arrow (truncationFiltration_d_preserves K p i j)⟩ }
  shape := fun i j hij ↦ FilteredObject.forget.map_injective (K.shape i j hij)
  d_comp_d' := fun i j k hij hjk ↦
    FilteredObject.forget.map_injective (K.d_comp_d' i j k hij hjk)

/-- The truncation filtration has finite filtrations in every degree. -/
theorem truncationFiltration_hasFiniteFiltrations (K : CochainComplex 𝒜 ℤ) :
    (truncationFiltration K).HasFiniteFiltrations := sorry

namespace TruncationFiltration

/-- Below the cutoff, the stage term has the explicit identity-subobject identification with the
original term. -/
noncomputable def stageTermIsoOfLT
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    ((K.truncationFiltration).stage p).X n ≅ K.X n := by
  change (truncationFiltrationSubobject K p n : 𝒜) ≅ K.X n
  rw [truncationFiltrationSubobject, if_pos hn, Subobject.top_eq_id]
  exact Subobject.underlyingIso (𝟙 (K.X n))

/-- The forward map of `stageTermIsoOfLT` is the corresponding stage inclusion component. -/
theorem stageTermIsoOfLT_hom
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    (stageTermIsoOfLT K p n hn).hom =
      ((K.truncationFiltration).stageInclusion p).f n := sorry

/-- At the cutoff degree, the stage term has the explicit kernel-to-cycles identification. -/
noncomputable def stageTermIsoCycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    ((K.truncationFiltration).stage p).X (-p) ≅ K.cycles (-p) := by
  change (truncationFiltrationSubobject K p (-p) : 𝒜) ≅ K.cycles (-p)
  rw [truncationFiltrationSubobject, if_neg (lt_irrefl _), if_pos rfl]
  let S : ShortComplex 𝒜 := K.sc' (-p - 1) (-p) (-p + 1)
  let hprev : (ComplexShape.up ℤ).prev (-p) = -p - 1 := by
    apply ComplexShape.prev_eq'
    simpa [ComplexShape.up, ComplexShape.up'] using (show (-p - 1 : ℤ) + 1 = -p by omega)
  let hnext : (ComplexShape.up ℤ).next (-p) = -p + 1 := by
    apply ComplexShape.next_eq'
    simpa [ComplexShape.up, ComplexShape.up'] using (show (-p : ℤ) + 1 = -p + 1 by omega)
  exact kernelSubobjectIso (K.d (-p) (-p + 1)) ≪≫ S.cyclesIsoKernel.symm ≪≫
    (K.cyclesIsoSc' (-p - 1) (-p) (-p + 1) hprev hnext).symm

/-- The forward map of `stageTermIsoCycles` followed by the cycles inclusion is the stage
inclusion component at the cutoff. -/
theorem stageTermIsoCycles_hom_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (stageTermIsoCycles K p).hom ≫ K.iCycles (-p) =
      ((K.truncationFiltration).stageInclusion p).f (-p) := sorry

/-- Above the cutoff, the truncation-filtration stage vanishes. -/
theorem termIsZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero (((K.truncationFiltration).stage p).X n) := by
  change IsZero ((truncationFiltrationSubobject K p n : 𝒜))
  rw [truncationFiltrationSubobject, if_neg (not_lt_of_ge (le_of_lt hn))]
  rw [if_neg (by omega : ¬ n = -p)]
  exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- An index on or below the cutoff is represented by `embeddingUpIntLE`. -/
theorem toNatSub_eq
    (p n : ℤ) (hn : n ≤ -p) :
    (embeddingUpIntLE (-p)).f (Int.toNat (-p - n)) = n := by
  rw [ComplexShape.embeddingUpIntLE_f]
  omega

/-- Below the cutoff, the canonical truncation term is the original term. -/
def truncTermIsoOfLT
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : n < -p) :
    (K.truncLE (-p)).X n ≅ K.X n :=
  let i : ℕ := Int.toNat (-p - n)
  let hi' : (embeddingUpIntLE (-p)).f i = n := toNatSub_eq p n (le_of_lt hn)
  let hboundary : ¬ (embeddingUpIntLE (-p)).BoundaryLE i := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    intro hi0
    have : -p = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntLE_f] using hi'
    omega
  HomologicalComplex.truncLEXIso K (embeddingUpIntLE (-p)) hi' hboundary

/-- At the cutoff, the canonical truncation term is the cycles object. -/
def truncTermIsoCycles
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.truncLE (-p)).X (-p) ≅ K.cycles (-p) :=
  let hi' : (embeddingUpIntLE (-p)).f 0 = -p := by
    simp [ComplexShape.embeddingUpIntLE_f]
  let hboundary : (embeddingUpIntLE (-p)).BoundaryLE 0 := by
    simpa using (ComplexShape.boundaryLE_embeddingUpIntLE_iff (-p) 0).2 rfl
  HomologicalComplex.truncLEXIsoCycles K (embeddingUpIntLE (-p)) hi' hboundary

/-- Above the cutoff, the canonical truncation term vanishes. -/
theorem truncTermIsZero_of_gt
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) (hn : -p < n) :
    IsZero ((K.truncLE (-p)).X n) := by
  exact (K.truncLE (-p)).isZero_of_isStrictlyLE (-p) n hn

/-- Degreewise, the truncation-filtration stage agrees with the canonical upper truncation. -/
noncomputable def componentIso
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    ((K.truncationFiltration).stage p).X n ≅ (K.truncLE (-p)).X n := by
  by_cases hn_lt : n < -p
  · exact stageTermIsoOfLT K p n hn_lt ≪≫
      (truncTermIsoOfLT K p n hn_lt).symm
  · by_cases hn_eq : n = -p
    · subst hn_eq
      exact stageTermIsoCycles K p ≪≫
        (truncTermIsoCycles K p).symm
    · have hn_gt : -p < n := by omega
      exact (termIsZero_of_gt K p n hn_gt).isoZero ≪≫
        (truncTermIsZero_of_gt K p n hn_gt).isoZero.symm

/-- Degreewise, the chosen comparison factors the stage inclusion through
`K.ιTruncLE (-p)`. -/
theorem componentIso_hom_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p n : ℤ) :
    (componentIso K p n).hom ≫ (K.ιTruncLE (-p)).f n =
      ((K.truncationFiltration).stageInclusion p).f n := sorry

/-- The degreewise comparison commutes with the differentials of the filtration stage and the
canonical upper truncation. -/
theorem componentIso_hom_comm_d
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) {i j : ℤ}
    (_ : (ComplexShape.up ℤ).Rel i j) :
    (componentIso K p i).hom ≫ (K.truncLE (-p)).d i j =
      ((K.truncationFiltration).stage p).d i j ≫ (componentIso K p j).hom := sorry

/-- The `p`-th truncation-filtration stage is identified with the canonical upper truncation
`K.truncLE (-p)`. This is the reusable owner of the stage comparison; consumers should use its
factorization specification rather than choose a comparison map. -/
@[stacks 015X "truncation-filtration stage comparison"]
noncomputable def stageIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (K.truncationFiltration).stage p ≅ K.truncLE (-p) :=
  HomologicalComplex.Hom.isoOfComponents
    (componentIso K p)
    (fun i j hij ↦ componentIso_hom_comm_d K p hij)

/-- The forward map of `stageIso` factors the stage inclusion through the canonical upper
truncation inclusion. -/
theorem stageIso_hom_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) :
    (stageIso K p).hom ≫ K.ιTruncLE (-p) =
      (K.truncationFiltration).stageInclusion p := sorry

/-- Stage comparison for the truncation filtration agrees with the canonical transition between
the corresponding upper truncations. -/
theorem stageComparison_hom
    (K : CochainComplex 𝒜 ℤ) {p q : ℤ} (hpq : p ≤ q) :
    (K.truncationFiltration).stageComparison hpq ≫ (stageIso K p).hom =
      (stageIso K q).hom ≫ K.truncLEMapOfLE (neg_le_neg hpq) := sorry

/-- A map to the canonical upper truncation is the forward map of `stageIso` when it has the
same composite with the truncation inclusion. -/
theorem hom_eq_of_comp_inclusion
    (K : CochainComplex 𝒜 ℤ) (p : ℤ)
    (φ : (K.truncationFiltration).stage p ⟶ K.truncLE (-p))
    (hφ : φ ≫ K.ιTruncLE (-p) = (K.truncationFiltration).stageInclusion p) :
    φ = (stageIso K p).hom := sorry

end TruncationFiltration

end Filtrations

end CochainComplex

end CategoryTheory
