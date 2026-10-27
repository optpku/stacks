/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Diagrams in Preadditive Categories

This leaf owns the algebraic telescope map of a sequential diagram and the
finite-prefix systems used to analyse it.  It is independent of
pretriangulated and derived categories: only preadditive structure, finite
biproducts, and the colimits explicitly requested by each construction are
used here.

The `FinitePrefix` namespace contains one fixed, recursively bracketed model
of the finite partial sums.  Its maps are useful when a downstream argument
needs concrete finite-stage calculations; `telescopeMap_shortExact` is the
high-level consequence for abelian categories with exact sequential colimits.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory.Limits.Sequential

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The algebraic telescope endomorphism `1 - f` of the coproduct of a sequential diagram. -/
@[stacks 093W]
def telescopeMap (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    ∐ K.obj ⟶ ∐ K.obj :=
  𝟙 _ - Sigma.map' Nat.succ (fun n ↦ K.map (homOfLE (Nat.le_succ n)))

/-- The `n`th summand of `telescopeMap K` is the difference of the identity and the successor
transition. -/
@[reassoc]
theorem ι_comp_telescopeMap (K : ℕ ⥤ C) [HasCoproduct K.obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ telescopeMap K =
      Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  simp [telescopeMap, Preadditive.comp_sub]

attribute [simp] ι_comp_telescopeMap_assoc

/-- The telescope endomorphism is natural in a morphism of sequential diagrams. -/
@[reassoc]
theorem telescopeMap_naturality {K L : ℕ ⥤ C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    telescopeMap K ≫ Sigma.map φ.app = Sigma.map φ.app ≫ telescopeMap L := by
  set_option backward.isDefEq.respectTransparency false in
    apply Sigma.hom_ext
    intro n
    simp only [ι_comp_telescopeMap_assoc, Sigma.ι_map_assoc, Preadditive.sub_comp,
      Category.assoc, Sigma.ι_map, ι_comp_telescopeMap, Preadditive.comp_sub]
    rw [φ.naturality_assoc]

/-- The telescope map vanishes after a coproduct descent whose legs form a cocone over the
sequential diagram. -/
@[reassoc]
theorem telescopeMap_comp_sigmaDesc (K : ℕ ⥤ C) [HasCoproduct K.obj] {X : C}
    (ι : ∀ n, K.obj n ⟶ X)
    (hι : ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) :
    telescopeMap K ≫ Sigma.desc ι = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    apply Sigma.hom_ext
    intro n
    simp [ι_comp_telescopeMap_assoc, Preadditive.sub_comp, Category.assoc,
      hι n]

/-- The telescope map vanishes after the coproduct descent of any cocone over the sequential
diagram. -/
@[reassoc]
theorem telescopeMap_comp_sigmaDesc_of_cocone (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (c : Cocone K) :
    telescopeMap K ≫ Sigma.desc (fun n ↦ c.ι.app n) = 0 := by
  exact telescopeMap_comp_sigmaDesc K _ (fun n ↦ c.w (homOfLE (Nat.le_succ n)))

/-- The canonical short complex whose first map is the telescope endomorphism and whose
second map is the coproduct descent to the sequential colimit. -/
@[stacks 093W]
noncomputable def telescopeShortComplex (K : ℕ ⥤ C) [HasCoproduct K.obj] [HasColimit K] :
    ShortComplex C :=
  ShortComplex.mk (telescopeMap K)
    (Sigma.desc (colimit.ι K))
    (telescopeMap_comp_sigmaDesc K (colimit.ι K)
      (fun n ↦ colimit.w K (homOfLE (Nat.le_succ n))))

/-- The projection from the coproduct of a sequential diagram to its `k`th object, retaining
summands indexed by `i ≤ k` through their transition maps and killing later summands. -/
noncomputable def prefixProjection (K : ℕ ⥤ C) [HasCoproduct K.obj] (k : ℕ) :
    ∐ K.obj ⟶ K.obj k :=
  Sigma.desc fun i ↦ if h : i ≤ k then K.map (homOfLE h) else 0

/-- A retained summand maps through `prefixProjection` by its sequential transition map. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_of_le (K : ℕ ⥤ C) [HasCoproduct K.obj]
    {i k : ℕ} (h : i ≤ k) :
    Sigma.ι K.obj i ≫ prefixProjection K k = K.map (homOfLE h) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [prefixProjection, h]

/-- A summand after the selected prefix is killed by `prefixProjection`. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_of_not_le (K : ℕ ⥤ C) [HasCoproduct K.obj]
    {i k : ℕ} (h : ¬ i ≤ k) :
    Sigma.ι K.obj i ≫ prefixProjection K k = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    simp [prefixProjection, h]

/-- The `k`th summand is sent identically to the `k`th object by `prefixProjection`. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_self (K : ℕ ⥤ C) [HasCoproduct K.obj] (k : ℕ) :
    Sigma.ι K.obj k ≫ prefixProjection K k = 𝟙 (K.obj k) := by
  simpa using sigma_ι_comp_prefixProjection_of_le K (le_refl k)

end

namespace FinitePrefix

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- A recursively bracketed finite partial sum of a sequential diagram.  `obj K n` contains the
terms with indices strictly smaller than `n`. -/
def obj (K : ℕ ⥤ C) : ℕ → C
  | 0 => 0
  | n + 1 => obj K n ⊞ K.obj n

/-- The canonical inclusion of a finite prefix into the prefix with one additional summand. -/
def inclusion (K : ℕ ⥤ C) (n : ℕ) :
    obj K n ⟶ obj K (n + 1) :=
  biprod.inl

/-- The inclusion of the newest summand into a nonempty finite prefix. -/
def lastι (K : ℕ ⥤ C) (n : ℕ) :
    K.obj n ⟶ obj K (n + 1) :=
  biprod.inr

/-- The recursive projection from a nonempty finite prefix to its newest quotient summand. -/
def stageProjection (K : ℕ ⥤ C) :
    (n : ℕ) → obj K (n + 1) ⟶ K.obj n
  | 0 => biprod.snd
  | n + 1 =>
      biprod.desc
        (stageProjection K n ≫ K.map (homOfLE (Nat.le_succ n)))
        (𝟙 _)

/-- The finite-stage telescope map from one partial sum to the next. -/
def stageMap (K : ℕ ⥤ C) :
    (n : ℕ) → obj K n ⟶ obj K (n + 1)
  | 0 => inclusion K 0
  | n + 1 =>
      biprod.desc
        (stageMap K n ≫ inclusion K (n + 1))
        (lastι K n ≫ inclusion K (n + 1) -
          K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))

/-- A recursive retraction of the finite-stage telescope map. -/
def stageRetraction (K : ℕ ⥤ C) :
    (n : ℕ) → obj K (n + 1) ⟶ obj K n
  | 0 => biprod.fst
  | n + 1 =>
      biprod.desc
        (biprod.lift (stageRetraction K n) (stageProjection K n))
        0

/-- The newest summand maps isomorphically to its stage quotient. -/
theorem lastι_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    lastι K n ≫ stageProjection K n = 𝟙 _ := by
  set_option backward.isDefEq.respectTransparency false in
    cases n <;> simp [lastι, stageProjection]

/-- The recursive stage retraction annihilates the newest summand. -/
theorem lastι_comp_stageRetraction (K : ℕ ⥤ C) (n : ℕ) :
    lastι K n ≫ stageRetraction K n = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    cases n <;> simp [lastι, stageRetraction]

/-- The old-prefix inclusion followed by the next stage projection is the previous projection
followed by the sequential transition. -/
theorem inclusion_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    inclusion K (n + 1) ≫ stageProjection K (n + 1) =
      stageProjection K n ≫ K.map (homOfLE (Nat.le_succ n)) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [inclusion, stageProjection]

/-- The correction branch of a finite-stage telescope map vanishes after the next stage
projection. -/
theorem correction_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    ((lastι K n ≫ inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))) ≫
      stageProjection K (n + 1) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.sub_comp, Category.assoc, inclusion_comp_stageProjection,
      reassoc_of% (lastι_comp_stageProjection K n), lastι_comp_stageProjection]

/-- Every finite-stage telescope map is annihilated by its stage projection. -/
theorem stageMap_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    stageMap K n ≫ stageProjection K n = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    induction n with
    | zero =>
        simp [stageMap, inclusion, stageProjection]
    | succ n ih =>
        apply biprod.hom_ext'
        · simp [stageMap, Category.assoc, inclusion_comp_stageProjection, reassoc_of% ih]
        · simpa only [stageMap, biprod.inr_desc_assoc, comp_zero] using
            correction_comp_stageProjection K n

/-- The explicit stage retraction is a left inverse of the finite-stage telescope map. -/
theorem stageMap_comp_stageRetraction (K : ℕ ⥤ C) (n : ℕ) :
    stageMap K n ≫ stageRetraction K n = 𝟙 _ := by
  set_option backward.isDefEq.respectTransparency false in
    induction n with
    | zero =>
        simp [stageMap, inclusion, stageRetraction]
    | succ n ih =>
        have h : inclusion K (n + 1) ≫ stageRetraction K (n + 1) =
            biprod.lift (stageRetraction K n) (stageProjection K n) := by
          simp [inclusion, stageRetraction]
        dsimp only [obj]
        apply biprod.hom_ext'
        · rw [stageMap, biprod.inl_desc_assoc, Category.comp_id, Category.assoc, h]
          apply biprod.hom_ext
          · simp [Category.assoc, ih]
          · simp [Category.assoc, stageMap_comp_stageProjection]
        · rw [stageMap, biprod.inr_desc_assoc, Category.comp_id, Preadditive.sub_comp,
            Category.assoc, h, Category.assoc, lastι_comp_stageRetraction,
            comp_zero, sub_zero]
          apply biprod.hom_ext
          · simp [Category.assoc, lastι_comp_stageRetraction]
          · simp [Category.assoc, lastι_comp_stageProjection]

/-- Every finite-stage telescope map is split mono. -/
theorem stageSplitMono (K : ℕ ⥤ C) (n : ℕ) :
    IsSplitMono (stageMap K n) := by
  exact IsSplitMono.mk' ⟨stageRetraction K n, stageMap_comp_stageRetraction K n⟩

/-- Every finite-stage telescope map is mono. -/
theorem stageMono (K : ℕ ⥤ C) (n : ℕ) :
    Mono (stageMap K n) := by
  letI := stageSplitMono K n
  infer_instance

/-- The chosen finite prefixes form a sequential diagram. -/
def source (K : ℕ ⥤ C) : ℕ ⥤ C :=
  Functor.ofSequence (fun n ↦ inclusion K n)

/-- The shifted finite prefixes form a second sequential diagram. -/
def target (K : ℕ ⥤ C) : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n ↦ obj K (n + 1))
    (fun n ↦ inclusion K (n + 1))

/-- The finite-stage telescope maps obey the successor naturality relation. -/
theorem stageNaturality (K : ℕ ⥤ C) (n : ℕ) :
    inclusion K n ≫ stageMap K (n + 1) =
      stageMap K n ≫ inclusion K (n + 1) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [inclusion, stageMap]

/-- The same relation, expressed using the source and target sequence functors. -/
theorem stageNatTrans_naturality (K : ℕ ⥤ C) (n : ℕ) :
    (source K).map (homOfLE (Nat.le_succ n)) ≫ stageMap K (n + 1) =
      stageMap K n ≫ (target K).map (homOfLE (Nat.le_succ n)) := by
  set_option backward.isDefEq.respectTransparency false in
    simpa [source, target] using stageNaturality K n

/-- The finite-stage telescope maps assemble into a natural transformation of sequential
diagrams. -/
def stageNatTrans (K : ℕ ⥤ C) : source K ⟶ target K :=
  NatTrans.ofSequence (fun n ↦ stageMap K n) (stageNatTrans_naturality K)

/-- The canonical map from a finite prefix into the coproduct of the whole sequence. -/
def toCoproduct (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    (n : ℕ) → obj K n ⟶ ∐ K.obj
  | 0 => 0
  | n + 1 => biprod.desc (toCoproduct K n) (Sigma.ι K.obj n)

/-- A prefix inclusion is compatible with the maps into the coproduct. -/
theorem inclusion_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    inclusion K n ≫ toCoproduct K (n + 1) = toCoproduct K n := by
  set_option backward.isDefEq.respectTransparency false in
    simp [inclusion, toCoproduct]

/-- The newest summand of a prefix maps to the corresponding coproduct inclusion. -/
theorem lastι_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    lastι K n ≫ toCoproduct K (n + 1) = Sigma.ι K.obj n := by
  set_option backward.isDefEq.respectTransparency false in
    simp [lastι, toCoproduct]

/-- The correction branch maps to the difference of the two adjacent coproduct summands. -/
theorem correction_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    ((lastι K n ≫ inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))) ≫
      toCoproduct K (n + 2) =
        Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := by
  set_option backward.isDefEq.respectTransparency false in
    simp [Preadditive.sub_comp, Category.assoc, inclusion_comp_toCoproduct,
      lastι_comp_toCoproduct]

/-- The maps from finite prefixes to the coproduct intertwine the finite-stage and global
telescope maps. -/
theorem toCoproduct_comp_telescopeMap (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    toCoproduct K n ≫ telescopeMap K = stageMap K n ≫ toCoproduct K (n + 1) := by
  set_option backward.isDefEq.respectTransparency false in
    induction n with
    | zero =>
        simp [toCoproduct, stageMap, inclusion]
    | succ n ih =>
        apply biprod.hom_ext'
        · change inclusion K n ≫ (toCoproduct K (n + 1) ≫ telescopeMap K) =
            inclusion K n ≫ (stageMap K (n + 1) ≫ toCoproduct K (n + 2))
          rw [← Category.assoc, inclusion_comp_toCoproduct, ← Category.assoc,
            stageNaturality, Category.assoc, inclusion_comp_toCoproduct]
          exact ih
        · simpa only [toCoproduct, biprod.inr_desc_assoc, stageMap,
            ι_comp_telescopeMap] using (correction_comp_toCoproduct K n).symm

/-- The source-prefix cocone legs satisfy their successor compatibility relation. -/
theorem sourceCocone_naturality (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    (source K).map (homOfLE (Nat.le_succ n)) ≫ toCoproduct K (n + 1) =
      toCoproduct K n ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
        (homOfLE (Nat.le_succ n)) := by
  set_option backward.isDefEq.respectTransparency false in
    simpa [source] using inclusion_comp_toCoproduct K n

/-- The target-prefix cocone legs satisfy their successor compatibility relation. -/
theorem targetCocone_naturality (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    (target K).map (homOfLE (Nat.le_succ n)) ≫ toCoproduct K (n + 2) =
      toCoproduct K (n + 1) ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
        (homOfLE (Nat.le_succ n)) := by
  set_option backward.isDefEq.respectTransparency false in
    simpa [target] using inclusion_comp_toCoproduct K (n + 1)

/-- The cocone from the source-prefix sequence to the coproduct. -/
def sourceCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    Cocone (source K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence (fun n ↦ toCoproduct K n) (sourceCocone_naturality K)

/-- The cocone from the target-prefix sequence to the coproduct. -/
def targetCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    Cocone (target K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence (fun n ↦ toCoproduct K (n + 1)) (targetCocone_naturality K)

/-- The explicit descendant from the coproduct for a cocone on the source-prefix sequence. -/
def sourceDesc (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) :
    (∐ K.obj) ⟶ s.pt :=
  Sigma.desc (fun i ↦ lastι K i ≫ s.ι.app (i + 1))

/-- The source-prefix descendant has the required components. -/
@[simp, reassoc]
theorem sourceDesc_fac (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) (n : ℕ) :
    toCoproduct K n ≫ sourceDesc K s = s.ι.app n := by
  set_option backward.isDefEq.respectTransparency false in
    induction n with
    | zero =>
        exact (isZero_zero C).eq_of_src _ _
    | succ n ih =>
        apply biprod.hom_ext'
        · simp only [toCoproduct, biprod.inl_desc_assoc, ih]
          simpa [source, inclusion] using (s.w (homOfLE (Nat.le_succ n))).symm
        · simp [toCoproduct, sourceDesc, lastι]

/-- The source-prefix descendant is the unique map satisfying the cocone equations. -/
theorem sourceDesc_uniq (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) (m : (sourceCocone K).pt ⟶ s.pt)
    (hm : ∀ n, (sourceCocone K).ι.app n ≫ m = s.ι.app n) :
    m = sourceDesc K s := by
  set_option backward.isDefEq.respectTransparency false in
    apply Sigma.hom_ext
    intro i
    have h : toCoproduct K (i + 1) ≫ m = s.ι.app (i + 1) := hm (i + 1)
    rw [← lastι_comp_toCoproduct K i]
    simp only [Category.assoc, h, sourceDesc_fac]

/-- The coproduct is a colimit of the source-prefix sequential diagram. -/
noncomputable def sourceIsColimit (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    IsColimit (sourceCocone K) :=
  IsColimit.mk
    (fun s ↦ sourceDesc K s)
    (fun s n ↦ sourceDesc_fac K s n)
    (fun s m hm ↦ sourceDesc_uniq K s m hm)

/-- The explicit descendant from the coproduct for a cocone on the target-prefix sequence. -/
def targetDesc (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) :
    (∐ K.obj) ⟶ s.pt :=
  Sigma.desc (fun i ↦ lastι K i ≫ s.ι.app i)

/-- The target-prefix descendant has the required components. -/
@[simp, reassoc]
theorem targetDesc_fac (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) (n : ℕ) :
    toCoproduct K (n + 1) ≫ targetDesc K s = s.ι.app n := by
  set_option backward.isDefEq.respectTransparency false in
    induction n with
    | zero =>
        apply biprod.hom_ext'
        · exact (isZero_zero C).eq_of_src _ _
        · simp [toCoproduct, targetDesc, lastι]
    | succ n ih =>
        apply biprod.hom_ext'
        · change inclusion K (n + 1) ≫ (toCoproduct K (n + 2) ≫ targetDesc K s) =
            inclusion K (n + 1) ≫ s.ι.app (n + 1)
          rw [← Category.assoc, inclusion_comp_toCoproduct, ih]
          simpa [target, inclusion] using (s.w (homOfLE (Nat.le_succ n))).symm
        · simp [toCoproduct, targetDesc, lastι]

/-- The target-prefix descendant is the unique map satisfying the cocone equations. -/
theorem targetDesc_uniq (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) (m : (targetCocone K).pt ⟶ s.pt)
    (hm : ∀ n, (targetCocone K).ι.app n ≫ m = s.ι.app n) :
    m = targetDesc K s := by
  set_option backward.isDefEq.respectTransparency false in
    apply Sigma.hom_ext
    intro i
    have h : toCoproduct K (i + 1) ≫ m = s.ι.app i := hm i
    rw [← lastι_comp_toCoproduct K i]
    simp only [Category.assoc, h, targetDesc_fac]

/-- The coproduct is a colimit of the target-prefix sequential diagram. -/
noncomputable def targetIsColimit (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    IsColimit (targetCocone K) :=
  IsColimit.mk
    (fun s ↦ targetDesc K s)
    (fun s n ↦ targetDesc_fac K s n)
    (fun s m hm ↦ targetDesc_uniq K s m hm)

/-- The source and target finite-prefix cocones intertwine the finite-stage and global telescope
maps. -/
theorem coconeCompat (K : ℕ ⥤ C) [HasCoproduct K.obj] (n : ℕ) :
    (sourceCocone K).ι.app n ≫ telescopeMap K =
      (stageNatTrans K).app n ≫ (targetCocone K).ι.app n := by
  exact toCoproduct_comp_telescopeMap K n

end

end FinitePrefix

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimitsOfShape ℕ C]

/-- The telescope short complex of a sequential diagram is short exact when sequential colimits
are exact.  This is the high-level API; `FinitePrefix` exposes the concrete finite-stage model
used to establish its monomorphism assertion. -/
@[stacks 093W]
theorem telescopeMap_shortExact [HasExactColimitsOfShape ℕ C] (K : ℕ ⥤ C)
    [HasCoproduct K.obj] :
    (telescopeShortComplex K).ShortExact := by
  set_option backward.isDefEq.respectTransparency false in
    let c {X : C} (f : ∐ K.obj ⟶ X) (hf : telescopeMap K ≫ f = 0) : Cocone K :=
      Cocone.mk X (NatTrans.ofSequence (fun n ↦ Sigma.ι K.obj n ≫ f) (fun n ↦ by
        have h := congrArg (fun g ↦ Sigma.ι K.obj n ≫ g) hf
        have h' : Sigma.ι K.obj n ≫ f =
            K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) ≫ f := by
          apply sub_eq_zero.mp
          simpa only [ι_comp_telescopeMap_assoc, Preadditive.sub_comp,
            Category.assoc, comp_zero] using h
        simpa [Functor.const] using h'.symm))
    have hc : IsColimit (CokernelCofork.ofπ (Sigma.desc (colimit.ι K))
        (telescopeMap_comp_sigmaDesc K (colimit.ι K)
          (fun n ↦ colimit.w K (homOfLE (Nat.le_succ n))))) := by
      refine CokernelCofork.IsColimit.ofπ _ _
        (fun {X} f hf ↦ colimit.desc K (c f hf)) ?_ ?_
      · intro X f hf
        apply Sigma.hom_ext
        intro n
        simp [c]
      · intro X f hf m hm
        apply colimit.hom_ext
        intro n
        have h := congrArg (fun g ↦ Sigma.ι K.obj n ≫ g) hm
        simpa [Category.assoc, Sigma.ι_desc, c] using h
    letI : ∀ n, Mono ((FinitePrefix.stageNatTrans K).app n) :=
      fun n ↦ FinitePrefix.stageMono K n
    letI : Mono (FinitePrefix.stageNatTrans K) := NatTrans.mono_of_mono_app _
    have hm : Mono (telescopeMap K) :=
      colim.map_mono' (FinitePrefix.stageNatTrans K) (FinitePrefix.sourceIsColimit K)
        (FinitePrefix.targetIsColimit K) (telescopeMap K) (FinitePrefix.coconeCompat K)
    exact ShortComplex.ShortExact.mk'
      ((telescopeShortComplex K).exact_of_g_is_cokernel hc) hm
      (epi_of_isColimit_cofork hc)

end

end CategoryTheory.Limits.Sequential
