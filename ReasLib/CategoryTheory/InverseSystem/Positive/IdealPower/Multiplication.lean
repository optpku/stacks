/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Presentation
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication diagrams on ideal-power quotient towers

For a representative `a ∈ I ^ d`, scalar multiplication on `F (d + n + 1)` descends along the
quotient transition to a map `F (n + 1) ⟶ F (d + n + 1)`.  The defining transition equation makes
this raising-degree map unique; its restriction supplies maps between the ideal-power terms.
`Presentation.multiplication` constructs these maps using kernels and normal epi and mono
universal properties, available in particular for modules and sheaves of modules.  The resulting
successor-row map is exposed for cohomological naturality arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.PNatInverseSystem.IdealPower

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- Multiplication maps on a presented ideal-power quotient tower.

For `a ∈ I ^ d`, `stageMap` is the map induced on the quotient by scalar multiplication with
`a`; `termMap` is its restriction to the ideal-power terms. -/
@[stacks 0GYM "multiplication diagrams for an ideal-power quotient tower"]
structure Multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F) where
  /-- Multiplication by a representative `a ∈ I ^ d` between ambient tower stages. -/
  stageMap : ∀ d n : ℕ, Ideal.AssociatedGraded.stage I A d →
    (F.stage (Nat.succPNat n) ⟶ F.stage (Nat.succPNat (d + n)))
  /-- The restriction of the ambient multiplication map to ideal-power terms. -/
  termMap : ∀ d n : ℕ, Ideal.AssociatedGraded.stage I A d →
    (terms P n ⟶ terms P (d + n))
  /-- The ambient map is the descent of scalar multiplication along the tower transition. -/
  transition_comp_stageMap : ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    F.degreeTransition d n ≫ stageMap d n a = (a : A) • 𝟙 _
  /-- The multiplication map on ideal-power terms is the restriction of the ambient map. -/
  termInclusion_comp_stageMap : ∀ (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    termInclusion P n ≫ stageMap d n a =
      termMap d n a ≫ termInclusion P (d + n)

section Construction

/-- The mono evidence used to obtain a normal presentation comes directly from `P`, without
selecting data from a separate existence assertion. -/
theorem Presentation.mono_termInclusion_from_presentation
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F) (n : ℕ) :
    Mono (termInclusion P n) := by
  cases n with
  | zero => exact inferInstanceAs (Mono (𝟙 (F.stage 1)))
  | succ n => exact (P.isQuotient.1 (Nat.succPNat n)).1

/-- Epimorphy is obtained from the supplied short exact rows and the functor laws. -/
theorem Presentation.epi_degreeTransition_from_presentation
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F) (d n : ℕ) :
    Epi (F.degreeTransition d n) := by
  obtain ⟨hι, hse⟩ := P.isQuotient.2
  have aux : ∀ (m : ℕ) (hnm : n ≤ m),
      Epi (OrderDualInverseSystem.transitionMap F (Nat.succPNat_mono hnm)) := by
    intro m hnm
    induction m, hnm using Nat.le_induction with
    | base =>
        change Epi (F.map (𝟙 (OrderDual.toDual (Nat.succPNat n))))
        rw [F.map_id]
        infer_instance
    | succ m hnm ih =>
        have hcomp :
            OrderDualInverseSystem.transitionMap F
                (Nat.succPNat_mono (hnm.trans (Nat.le_succ m))) =
              F.stepMap (Nat.succPNat m) ≫
                OrderDualInverseSystem.transitionMap F (Nat.succPNat_mono hnm) :=
          F.map_comp
            (homOfLE (OrderDual.toDual_le_toDual.mpr
              (PNat.lt_succ_self (Nat.succPNat m)).le))
            (homOfLE (OrderDual.toDual_le_toDual.mpr (Nat.succPNat_mono hnm)))
        rw [hcomp]
        exact epi_comp' (hse (Nat.succPNat m)).epi_g ih
  exact aux (d + n) (Nat.le_add_left n d)

/-- Scalar multiplication by `a ∈ I ^ d` kills every relation in the quotient transition
`F (d + n + 1) ⟶ F (n + 1)`. -/
theorem Presentation.relation_comp_smul
    [HasKernels C] [Balanced C]
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    {T : C} (k : T ⟶ F.stage (Nat.succPNat (d + n)))
    (hk : k ≫ F.degreeTransition d n = 0) :
    k ≫ ((a : A) • 𝟙 _) = 0 := sorry

variable [HasKernels C] [IsNormalEpiCategory C]

/-- The canonical raising-degree map, obtained by descending scalar multiplication on the later
stage through the quotient transition.  No lift of sections is chosen. -/
noncomputable def Presentation.multiplicationStageMap
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    F.stage (Nat.succPNat n) ⟶ F.stage (Nat.succPNat (d + n)) := by
  letI := P.epi_degreeTransition_from_presentation d n
  letI := normalEpiOfEpi (F.degreeTransition d n)
  exact (NormalEpi.desc' (F.degreeTransition d n) ((a : A) • 𝟙 _)
    (P.relation_comp_smul d n a _ (NormalEpi.w (f := F.degreeTransition d n)))).1

/-- The descended map computes on a representative in the later quotient as multiplication by
`a`. -/
@[reassoc]
theorem Presentation.transition_comp_multiplicationStageMap
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    F.degreeTransition d n ≫ P.multiplicationStageMap d n a = (a : A) • 𝟙 _ := by
  letI := P.epi_degreeTransition_from_presentation d n
  letI := normalEpiOfEpi (F.degreeTransition d n)
  exact (NormalEpi.desc' (F.degreeTransition d n) ((a : A) • 𝟙 _)
    (P.relation_comp_smul d n a _ (NormalEpi.w (f := F.degreeTransition d n)))).2

/-- The quotient computation determines the ambient multiplication map uniquely. -/
theorem Presentation.multiplicationStageMap_unique
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    (f : F.stage (Nat.succPNat n) ⟶ F.stage (Nat.succPNat (d + n)))
    (hf : F.degreeTransition d n ≫ f = (a : A) • 𝟙 _) :
    f = P.multiplicationStageMap d n a := by
  letI := P.epi_degreeTransition_from_presentation d n
  exact (cancel_epi (F.degreeTransition d n)).1
    (hf.trans (P.transition_comp_multiplicationStageMap d n a).symm)

/-- The descended scalar map sends `I ^ n F (n + 1)` into `I ^ (d + n) F (d + n + 1)`:
it is killed by every morphism killing that target subobject. -/
theorem Presentation.termInclusion_comp_multiplicationStageMap_comp_zero
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    {T : C} (q : F.stage (Nat.succPNat (d + n)) ⟶ T)
    (hq : termInclusion P (d + n) ≫ q = 0) :
    (termInclusion P n ≫ P.multiplicationStageMap d n a) ≫ q = 0 := sorry

variable [IsNormalMonoCategory C]

/-- Restriction of the descended scalar map to the presented ideal-power subobjects, including
the canonical degree-zero term. -/
noncomputable def Presentation.multiplicationTermMap
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    terms P n ⟶ terms P (d + n) := by
  letI := P.mono_termInclusion_from_presentation (d + n)
  letI := normalMonoOfMono (termInclusion P (d + n))
  exact (NormalMono.lift' (termInclusion P (d + n))
    (termInclusion P n ≫ P.multiplicationStageMap d n a)
    (P.termInclusion_comp_multiplicationStageMap_comp_zero d n a _
      (NormalMono.w (f := termInclusion P (d + n))))).1

/-- The restricted map computes as the ambient multiplication map after inclusion. -/
@[reassoc]
theorem Presentation.multiplicationTermMap_comp_termInclusion
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F)
    (d n : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    P.multiplicationTermMap d n a ≫ termInclusion P (d + n) =
      termInclusion P n ≫ P.multiplicationStageMap d n a := by
  letI := P.mono_termInclusion_from_presentation (d + n)
  letI := normalMonoOfMono (termInclusion P (d + n))
  exact (NormalMono.lift' (termInclusion P (d + n))
    (termInclusion P n ≫ P.multiplicationStageMap d n a)
    (P.termInclusion_comp_multiplicationStageMap_comp_zero d n a _
      (NormalMono.w (f := termInclusion P (d + n))))).2

/-- Canonical multiplication on a quotient presentation, constructed from the quotient and
ideal-subobject universal properties. -/
@[stacks 0GYK "canonical multiplication on an ideal-power quotient tower",
  stacks 0GYM "canonical multiplication on an ideal-power quotient tower"]
noncomputable def Presentation.multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Presentation I F) : Multiplication P where
  stageMap := P.multiplicationStageMap
  termMap := P.multiplicationTermMap
  transition_comp_stageMap := P.transition_comp_multiplicationStageMap
  termInclusion_comp_stageMap d n a :=
    (P.multiplicationTermMap_comp_termInclusion d n a).symm

/-- The two defining computation rules determine the whole multiplication package. -/
theorem Multiplication.eq_canonical
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) : μ = P.multiplication := sorry

end Construction

/-- Returning to the earlier stage after a multiplication map is scalar multiplication there. -/
theorem Multiplication.stageMap_comp_transition
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    μ.stageMap d n a ≫ F.degreeTransition d n = (a : A) • 𝟙 _ := sorry

/-- Ambient multiplication maps commute with the successor maps of the positive tower. -/
theorem Multiplication.stageMap_stepMap
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    μ.stageMap d (n + 1) a ≫ F.stepMap (Nat.succPNat (d + n)) =
      F.stepMap (Nat.succPNat n) ≫ μ.stageMap d n a := sorry

/-- Multiplication by a stage representative as a morphism between the corresponding successor
short exact rows. -/
@[stacks 0GYK "multiplication map between ideal-power quotient rows"]
def Multiplication.stepRowMap
    {I : Ideal A} {F : PNatInverseSystem C} {P : Presentation I F}
    (μ : Multiplication P) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    F.stepRow P.positiveTerms P.ι P.isQuotient.comp_zero (Nat.succPNat n) ⟶
      F.stepRow P.positiveTerms P.ι P.isQuotient.comp_zero
        (Nat.succPNat (d + n)) :=
  ShortComplex.homMk
    (μ.termMap d (n + 1) a)
    (μ.stageMap d (n + 1) a)
    (μ.stageMap d n a)
    (μ.termInclusion_comp_stageMap d (n + 1) a).symm
    (μ.stageMap_stepMap d n a)

end CategoryTheory.PNatInverseSystem.IdealPower
