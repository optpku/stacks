/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import ReasLib.Algebra.Homology.CochainComplex.SmallAcyclic.Termwise
public import ReasLib.CategoryTheory.Generator.CoproductCardinal
public import ReasLib.CategoryTheory.Abelian.SeparatorCoproduct.Refinement.Grothendieck
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.AcyclicReduction
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction.Core

public section

/-!
# Small Acyclic Complexes in Grothendieck Abelian Categories

Grothendieck abelian categories admit one cardinal controlling both nonzero small acyclic
subcomplexes and coproduct presentations of arbitrary acyclic complexes.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w v u

namespace CochainComplex.SmallAcyclic

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

private lemma exists_nonzero_cycle (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (hne : ¬ IsZero M) :
    ∃ (i : ℤ) (f : CategoryTheory.separator C ⟶ M.X i),
      f ≠ 0 ∧ f ≫ M.d i (i + 1) = 0 := by
  classical
  by_contra! h
  have hd (i : ℤ) : M.d i (i + 1) = 0 := by
    apply (isSeparator_separator C).def
    intro g
    rw [comp_zero]
    by_contra hg
    exact h (i + 1) (g ≫ M.d i (i + 1)) hg (by
      rw [Category.assoc, M.d_comp_d, comp_zero])
  apply hne
  rw [IsZero.iff_id_eq_zero]
  ext i
  have hd' (a b : ℤ) : M.d a b = 0 := by
    by_cases hab : a + 1 = b
    · subst b
      exact hd a
    · exact M.shape _ _ hab
  have hi := ((M.exactAt_iff' (j := i) (i := i - 1) (k := i + 1)
    (by simp) (by simp)).mp (hM i)).isZero_X₂ (hd' _ _) (hd i)
  exact hi.eq_of_src _ _

private abbrev CycleStage (M : CochainComplex C ℤ) (i : ℤ) :=
  Σ X : Subobject (M.X i),
    {Z : Subobject (X : C) // Z.arrow ≫ X.arrow ≫ M.d i (i + 1) = 0}

variable {C}

/-- The ambient subobject of a cycle stage. -/
private def CycleStage.X {M : CochainComplex C ℤ} {i : ℤ}
    (T : CycleStage C M i) : Subobject (M.X i) := T.1

/-- The cycle subobject inside the ambient subobject of a cycle stage. -/
private def CycleStage.Z {M : CochainComplex C ℤ} {i : ℤ}
    (T : CycleStage C M i) : Subobject (T.X : C) := T.2.val

/-- The cycle inclusion followed by the ambient differential vanishes. -/
private theorem CycleStage.zero {M : CochainComplex C ℤ} {i : ℤ}
    (T : CycleStage C M i) : T.Z.arrow ≫ T.X.arrow ≫ M.d i (i + 1) = 0 :=
  T.2.property

/-- The image of a generator morphism annihilated by the differential forms a cycle stage
whose cycle subobject is the whole image. -/
private def CycleStage.seed {M : CochainComplex C ℤ} {i : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X i) (hf : f ≫ M.d i (i + 1) = 0) :
    CycleStage C M i :=
  ⟨imageSubobject f, ⊤, by
    rw [← Category.assoc, Category.assoc, imageSubobject_arrow_comp_eq_zero hf, comp_zero]⟩

private def cycleLift {M : CochainComplex C ℤ} {i : ℤ} (T : CycleStage C M i) :
    (T.Z : C) ⟶ kernel (M.d i (i + 1)) :=
  kernel.lift _ (T.Z.arrow ≫ T.X.arrow) (by simpa only [Category.assoc] using T.zero)

private lemma cycleLift_mono {M : CochainComplex C ℤ} {i : ℤ}
    (T : CycleStage C M i) : Mono (cycleLift T) :=
  mono_of_mono_fac (kernel.lift_ι _ _ _)

private def ambientToCycles (M : CochainComplex C ℤ) (i : ℤ) :
    M.X (i - 1) ⟶ kernel (M.d i (i + 1)) :=
  kernel.lift _ (M.d (i - 1) i) (M.d_comp_d _ _ _)

private lemma ambientToCycles_epi {M : CochainComplex C ℤ} (hM : M.Acyclic) (i : ℤ) :
    Epi (ambientToCycles M i) :=
  ((M.exactAt_iff' (j := i) (i := i - 1) (k := i + 1)
    (by simp) (by simp)).mp (hM i)).epi_kernelLift

private def refinementFamily {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) :
    SeparatorEpi.Family (CategoryTheory.separator C)
      (pullback.snd (ambientToCycles M i) (cycleLift T)) := by
  -- Local instance justification (proof-local temporary data): Acyclicity makes this ambient-to-cycles arrow epic, allowing the separator-family construction on its pullback.
  haveI := ambientToCycles_epi hM i
  exact SeparatorEpi.Family.ofSeparator (isSeparator_separator C) _

private def lowerArrow {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) :
    ((refinementFamily hM T).refinement : C) ⟶ M.X (i - 1) :=
  (refinementFamily hM T).refinement.arrow ≫
    pullback.fst (ambientToCycles M i) (cycleLift T)

private lemma lowerArrow_mono {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : Mono (lowerArrow hM T) := by
  -- Local instance justification (proof-local temporary data): The fixed cycle inclusion is monomorphic, so the projection from its pullback is monomorphic.
  haveI := cycleLift_mono T
  exact mono_comp _ _

private def lowerX {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : Subobject (M.X (i - 1)) :=
  @Subobject.mk _ _ _ _ (lowerArrow hM T) (lowerArrow_mono hM T)

private def lowerIso {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) :
    (lowerX hM T : C) ≅ ((refinementFamily hM T).refinement : C) :=
  @Subobject.underlyingIso _ _ _ _ (lowerArrow hM T) (lowerArrow_mono hM T)

private def lowerToCycles {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : (lowerX hM T : C) ⟶ (T.Z : C) :=
  (lowerIso hM T).hom ≫ (refinementFamily hM T).toTarget

private lemma lowerToCycles_epi {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : Epi (lowerToCycles hM T) := by
  -- Local instance justification (proof-local temporary data): The ambient-to-cycles map is epic, as required by this refinement family’s epi_toTarget theorem.
  haveI := ambientToCycles_epi hM i
  -- Local instance justification (proof-local temporary data): The explicit refinement epimorphism is composed with lowerIso to obtain the displayed lower-stage epimorphism.
  haveI := (refinementFamily hM T).epi_toTarget
  exact epi_comp _ _

private def lowerDifferential {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : (lowerX hM T : C) ⟶ (T.X : C) :=
  lowerToCycles hM T ≫ T.Z.arrow

private lemma lower_comm {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) :
    (lowerX hM T).arrow ≫ M.d (i - 1) i = lowerDifferential hM T ≫ T.X.arrow := by
  change (@Subobject.mk _ _ _ _ (lowerArrow hM T) (lowerArrow_mono hM T)).arrow ≫
    M.d (i - 1) i = _
  rw [← @Subobject.underlyingIso_hom_comp_eq_mk _ _ _ _ (lowerArrow hM T)
    (lowerArrow_mono hM T)]
  dsimp only [lowerArrow, lowerDifferential, lowerToCycles,
    SeparatorEpi.Family.toTarget]
  simp only [Category.assoc]
  rw [← kernel.lift_ι (M.d i (i + 1)) (M.d (i - 1) i)]
  change (lowerIso hM T).hom ≫ (refinementFamily hM T).refinement.arrow ≫
    pullback.fst _ _ ≫ ambientToCycles M i ≫ kernel.ι _ = _
  rw [pullback.condition_assoc]
  simp only [cycleLift, kernel.lift_ι, Category.assoc]

/-- A cycle stage in an acyclic complex determines a preceding stage whose object lifts
the given cycles and whose cycle subobject is the kernel of the induced differential. -/
private def CycleStage.lower {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) : CycleStage C M (i - 1) :=
  ⟨lowerX hM T, kernelSubobject (lowerDifferential hM T), by
    have hi : i - 1 + 1 = i := by omega
    rw [hi, lower_comm hM T, ← Category.assoc,
      kernelSubobject_arrow_comp, zero_comp]⟩

private def zeroStage (M : CochainComplex C ℤ) (i : ℤ) : CycleStage C M i :=
  ⟨⊥, ⊤, by simp⟩

private def stages {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) : CycleStage C M i :=
  i.inductionOn' n (CycleStage.seed f hf) (fun j _ _ ↦ zeroStage M (j + 1))
    (fun _ _ T ↦ CycleStage.lower hM T)

private lemma stages_top {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0) :
    stages hM f hf n = CycleStage.seed f hf :=
  Int.inductionOn'_self ..

private lemma stages_lower {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : i ≤ n) :
    stages hM f hf (i - 1) = CycleStage.lower hM (stages hM f hf i) :=
  Int.inductionOn'_sub_one hi

private lemma stages_above {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : n < i) : stages hM f hf i = zeroStage M i := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
  exact Int.inductionOn'_add_one (by omega)

private lemma stages_cycles {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : n ≤ i) :
    (stages hM f hf i).Z = ⊤ := by
  rcases hi.eq_or_lt with rfl | hi
  · rw [stages_top]; rfl
  · rw [stages_above hM f hf i hi]; rfl

private lemma stage_d_factors {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i j : ℤ) :
    (stages hM f hf j).X.Factors ((stages hM f hf i).X.arrow ≫ M.d i j) := by
  by_cases hij : i + 1 = j
  · by_cases hi : j ≤ n
    · have he : i = j - 1 := by omega
      subst i
      rw [stages_lower hM f hf j hi]
      exact (Subobject.factors_iff _ _).mpr
        ⟨lowerDifferential hM (stages hM f hf j), (lower_comm hM _).symm⟩
    · subst j
      have hzero : (stages hM f hf i).X.arrow ≫ M.d i (i + 1) = 0 := by
        have ht := (stages hM f hf i).zero
        rw [stages_cycles hM f hf i (by omega)] at ht
        exact zero_of_epi_comp _ ht
      rw [hzero]
      exact (Subobject.factors_iff _ _).mpr ⟨0, zero_comp⟩
  · rw [M.shape i j hij, comp_zero]
    exact (Subobject.factors_iff _ _).mpr ⟨0, zero_comp⟩

private def termwise {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0) :
    HomologicalComplex.TermwiseSubcomplex M where
  X i := (stages hM f hf i).X
  d i j := (stages hM f hf j).X.factorThru
    ((stages hM f hf i).X.arrow ≫ M.d i j) (stage_d_factors hM f hf i j)
  comm i j := (Subobject.factorThru_arrow _ _ _).symm

private lemma termwise_d_lower {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : i ≤ n) :
    (termwise hM f hf).d (i - 1) i =
      eqToHom (congrArg (fun T : CycleStage C M (i - 1) ↦ (T.X : C))
        (stages_lower hM f hf i hi)) ≫ lowerDifferential hM (stages hM f hf i) := by
  apply (cancel_mono (stages hM f hf i).X.arrow).mp
  dsimp only [termwise]
  rw [Subobject.factorThru_arrow, Category.assoc, ← lower_comm, ← Category.assoc]
  exact (congrArg (fun a ↦ a ≫ M.d (i - 1) i)
    (Subobject.arrow_congr _ _ (congrArg CycleStage.X (stages_lower hM f hf i hi)))).symm

private lemma termwise_d_zero {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : n ≤ i) : (termwise hM f hf).d i (i + 1) = 0 := by
  apply (cancel_mono ((termwise hM f hf).X (i + 1)).arrow).mp
  rw [zero_comp, ← (termwise hM f hf).comm]
  have ht := (stages hM f hf i).zero
  rw [stages_cycles hM f hf i hi] at ht
  exact zero_of_epi_comp _ ht

private lemma termwise_kernel {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i j : ℤ) (hij : i + 1 = j) :
    (stages hM f hf i).Z = kernelSubobject ((termwise hM f hf).d i j) := by
  by_cases hj : j ≤ n
  · have he : i = j - 1 := by omega
    subst i
    have hk : kernelSubobject
        (((termwise hM f hf).X (j - 1)).arrow ≫ M.d (j - 1) j) =
        kernelSubobject ((termwise hM f hf).d (j - 1) j) := by
      apply le_antisymm
      · apply le_kernelSubobject
        apply zero_of_comp_mono ((termwise hM f hf).X j).arrow
        rw [Category.assoc, ← (termwise hM f hf).comm, kernelSubobject_arrow_comp]
      · apply le_kernelSubobject
        rw [(termwise hM f hf).comm, ← Category.assoc,
          kernelSubobject_arrow_comp, zero_comp]
    apply Eq.trans ?_ hk
    change (stages hM f hf (j - 1)).Z =
      kernelSubobject ((stages hM f hf (j - 1)).X.arrow ≫ M.d (j - 1) j)
    rw [stages_lower hM f hf j hj]
    dsimp only [CycleStage.lower, CycleStage.X, CycleStage.Z]
    apply le_antisymm
    · apply le_kernelSubobject
      rw [lower_comm, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
    · apply le_kernelSubobject
      apply zero_of_comp_mono (stages hM f hf j).X.arrow
      rw [Category.assoc, ← lower_comm, kernelSubobject_arrow_comp]
  · subst j
    rw [termwise_d_zero hM f hf i (by omega), kernelSubobject_zero,
      stages_cycles hM f hf i (by omega)]

private lemma termwise_exact {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) :
    imageSubobject ((termwise hM f hf).d (i - 1) i) =
      kernelSubobject ((termwise hM f hf).d i (i + 1)) := by
  rw [← termwise_kernel hM f hf i (i + 1) rfl]
  by_cases hi : i ≤ n
  · rw [termwise_d_lower hM f hf i hi, imageSubobject_iso_comp]
    change imageSubobject (lowerToCycles hM (stages hM f hf i) ≫
      (stages hM f hf i).Z.arrow) = _
    -- Local instance justification (proof-local temporary data): This lower-stage arrow is epic onto the cycle subobject, permitting the image-of-composite calculation.
    haveI := lowerToCycles_epi hM (stages hM f hf i)
    rw [imageSubobject_comp_eq_of_epi_left, imageSubobject_mono, Subobject.mk_arrow]
  · have hz : IsZero ((termwise hM f hf).X i : C) := by
      change IsZero ((stages hM f hf i).X : C)
      rw [stages_above hM f hf i (by omega)]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    -- Local instance justification (proof-local temporary data): This differential has a zero target and is therefore epic, so its image is the top subobject of that term.
    haveI := hz.epi ((termwise hM f hf).d (i - 1) i)
    rw [imageSubobject_eq_top_of_epi, stages_cycles hM f hf i (by omega)]

private lemma smallCardinal_le_of_mono {A B : C} (f : A ⟶ B) [Mono f] :
    Subobject.smallCardinal.{w} A ≤ Subobject.smallCardinal.{w} B := by
  apply Cardinal.lift_le.{max u v}.mp
  simpa only [Subobject.smallCardinal, Cardinal.lift_mk_shrink'] using
    Cardinal.lift_le.{w}.mpr (Subobject.cardinalMk_le_of_mono f)

private lemma lower_cardinal {M : CochainComplex C ℤ} (hM : M.Acyclic)
    {i : ℤ} (T : CycleStage C M i) :
    Subobject.smallCardinal.{w} (lowerX hM T : C) ≤
      KInjectiveResolution.Construction.growth C (Subobject.smallCardinal.{w} (T.X : C)) := by
  have hr := (refinementFamily hM T).cardinalMk_refinement_le
  rw [SeparatorEpi.familyBound,
    Subobject.cardinalMk_coprod_const_eq_coproductCardinal
      (CategoryTheory.separator C) (Subobject.smallCardinal.{w} (T.Z : C)) rfl] at hr
  have h := (Subobject.cardinalMk_eq_of_iso (lowerIso hM T)).le.trans hr
  have hm := Subobject.coproductCardinal_mono (CategoryTheory.separator C)
    (smallCardinal_le_of_mono T.Z.arrow)
  apply Cardinal.lift_le.{max u v}.mp
  simpa only [KInjectiveResolution.Construction.growth,
    KInjectiveResolution.Construction.generatorCopies,
    KInjectiveResolution.Construction.generator, Subobject.smallCardinal,
    Subobject.coproductCardinal, Cardinal.lift_mk_shrink'] using
      Cardinal.lift_le.{w}.mpr (h.trans hm)

private lemma growth_mono {κ μ : Cardinal.{w}} (h : κ ≤ μ) :
    KInjectiveResolution.Construction.growth C κ ≤
      KInjectiveResolution.Construction.growth C μ := by
  apply Cardinal.lift_le.{max u v}.mp
  simpa only [KInjectiveResolution.Construction.growth,
    KInjectiveResolution.Construction.generatorCopies,
    KInjectiveResolution.Construction.generator, Subobject.smallCardinal,
    Subobject.coproductCardinal, Cardinal.lift_mk_shrink'] using
      Cardinal.lift_le.{w}.mpr (Subobject.coproductCardinal_mono (CategoryTheory.separator C) h)

private lemma stages_cardinal {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0)
    (i : ℤ) (hi : i ≤ n) :
    Subobject.smallCardinal.{w} ((stages hM f hf i).X : C) ≤
      KInjectiveResolution.Construction.cardinalStage C (n - i).toNat := by
  refine Int.leInductionDown (m := n) ?_ ?_ i hi
  · rw [stages_top, sub_self, Int.toNat_zero]
    change Subobject.smallCardinal.{w} (imageSubobject f : C) ≤
      Subobject.smallCardinal.{w} (CategoryTheory.separator C)
    apply Cardinal.lift_le.{max u v}.mp
    simpa only [Subobject.smallCardinal, Cardinal.lift_mk_shrink'] using
      Cardinal.lift_le.{w}.mpr (Subobject.cardinalMk_image_le f)
  · intro j hj ih
    rw [stages_lower hM f hf j hj]
    change Subobject.smallCardinal.{w} (lowerX hM (stages hM f hf j) : C) ≤ _
    have he : (n - (j - 1)).toNat = (n - j).toNat + 1 := by omega
    rw [he, KInjectiveResolution.Construction.cardinalStage]
    exact (lower_cardinal hM _).trans (growth_mono ih)

private lemma termwise_boundedBy {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hf : f ≫ M.d n (n + 1) = 0) :
    BoundedBy (KInjectiveResolution.Construction.bound C) (termwise hM f hf).complex := by
  refine BoundedBy.ofTermwise _ _ n ?_ (termwise_exact hM f hf) ?_
  · intro i hi
    change IsZero ((stages hM f hf i).X : C)
    rw [stages_above hM f hf i hi]
    exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
  · intro i
    have hb : Subobject.smallCardinal.{w} ((stages hM f hf i).X : C) ≤
        KInjectiveResolution.Construction.bound C := by
      by_cases hi : i ≤ n
      · exact (stages_cardinal hM f hf i hi).trans
          ((Cardinal.le_sum (KInjectiveResolution.Construction.cardinalStage C) _).trans
            (le_add_left le_rfl))
      · have hz : IsZero ((stages hM f hf i).X : C) := by
          rw [stages_above hM f hf i (by omega)]
          exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
        have hm := @smallCardinal_le_of_mono _ _ _ _ _ (CategoryTheory.separator C)
          (0 : ((stages hM f hf i).X : C) ⟶ CategoryTheory.separator C) (hz.mono _)
        have h0 : Subobject.smallCardinal.{w} (CategoryTheory.separator C) ≤
            Cardinal.sum (KInjectiveResolution.Construction.cardinalStage C) := by
          simpa only [KInjectiveResolution.Construction.cardinalStage,
            KInjectiveResolution.Construction.generator] using
              Cardinal.le_sum (KInjectiveResolution.Construction.cardinalStage C) 0
        exact hm.trans (h0.trans (le_add_left le_rfl))
    change Cardinal.lift.{w} (Cardinal.mk (Subobject ((stages hM f hf i).X : C))) ≤ _
    simpa only [Subobject.smallCardinal, Cardinal.lift_mk_shrink'] using
      Cardinal.lift_le.{max u v}.mpr hb

private lemma termwise_not_isZero {M : CochainComplex C ℤ} (hM : M.Acyclic) {n : ℤ}
    (f : CategoryTheory.separator C ⟶ M.X n) (hfn : f ≠ 0)
    (hf : f ≫ M.d n (n + 1) = 0) : ¬ IsZero (termwise hM f hf).complex := by
  intro hz
  apply hfn
  have ht := (HomologicalComplex.eval C (.up ℤ) n).map_isZero hz
  change IsZero ((stages hM f hf n).X : C) at ht
  rw [stages_top] at ht
  rw [← imageSubobject_arrow_comp f, ht.eq_of_tgt (factorThruImageSubobject f) 0, zero_comp]

variable (C)

/-- The generator images and their recursively refined inverse images of kernels supply
nonzero bounded-above acyclic subcomplexes at the explicit countable cardinal bound. -/
def subcomplexSupplyOfGenerator :
    SubcomplexSupply C (KInjectiveResolution.Construction.bound C) := by
  classical
  exact {
  sub M hM hne :=
    let seed := exists_nonzero_cycle C M hM hne
    (termwise hM seed.choose_spec.choose seed.choose_spec.choose_spec.2).toSubobject
  not_isZero M hM hne := by
    let seed := exists_nonzero_cycle C M hM hne
    exact fun hz ↦ termwise_not_isZero hM seed.choose_spec.choose
      seed.choose_spec.choose_spec.1 seed.choose_spec.choose_spec.2
        ((termwise hM seed.choose_spec.choose seed.choose_spec.choose_spec.2).underlyingIso.isZero_iff.mp hz)
  boundedBy M hM hne := by
    let seed := exists_nonzero_cycle C M hM hne
    exact (termwise_boundedBy hM seed.choose_spec.choose seed.choose_spec.choose_spec.2).of_iso
      (termwise hM seed.choose_spec.choose seed.choose_spec.choose_spec.2).underlyingIso.symm }


/-- One cardinal uniformly controls nonzero small acyclic subcomplexes and
coproduct presentations of acyclic cochain complexes in a Grothendieck abelian category. The
chosen bound lives in a successor universe; the predicates it satisfies accept bounds in any
universe. -/
@[stacks 079K "uniform cardinal"]
theorem exists_bound :
    ∃ kappa : Cardinal.{max u v + 1},
      IsUniformBound C kappa := sorry

/-- The uniform small-acyclic-subcomplex consequence of `exists_bound`. -/
theorem exists_subcomplex_bound :
    ∃ kappa : Cardinal.{max u v + 1}, HasSubcomplexes C kappa := sorry

/-- The uniform acyclic coproduct-presentation consequence of `exists_bound`. -/
theorem exists_coproduct_presentation_bound :
    ∃ kappa : Cardinal.{max u v + 1}, HasCoproductPresentations C kappa := sorry

end CochainComplex.SmallAcyclic

