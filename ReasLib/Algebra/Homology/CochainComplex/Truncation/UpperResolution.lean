/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Transition

/-!
# Upper-Truncation Resolution Towers

This file owns direct systems of bounded-above, termwise-`P` resolutions of
the canonical upper truncations of a cochain complex.  Its naming and public
surface are dual to `CochainComplex.LowerTruncation.Resolution`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CochainComplex.UpperTruncation

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- 06XX (Lemma 13.29.1): the cutoff of the `n`th upper-truncation stage. -/
@[stacks 06XX]
abbrev index (n : ℕ) : ℤ := (n : ℤ) + 1

/-- Consecutive upper-truncation cutoffs occur in increasing order. -/
@[stacks 06XX]
theorem index_le_succ (n : ℕ) : index n ≤ index (n + 1) := sorry

/-- A canonical upper-truncation stage whose cutoff contains the cochain
degree `i`. -/
abbrev stageForDegree (i : ℤ) : ℕ := Int.toNat i

/-- The cutoff of `stageForDegree i` contains degree `i`. -/
theorem le_index_stageForDegree (i : ℤ) :
    i ≤ index (stageForDegree i) := sorry

/-- 06XX (Lemma 13.29.1): the `n`th canonical upper truncation of `K`. -/
@[stacks 06XX]
abbrev stage (K : CochainComplex A ℤ) (n : ℕ) : CochainComplex A ℤ :=
  K.truncLE (index n)

/-- 06XX (Lemma 13.29.1): the successor map in the canonical upper-truncation
diagram. -/
@[stacks 06XX]
noncomputable def step (K : CochainComplex A ℤ) (n : ℕ) :
    stage K n ⟶ stage K (n + 1) :=
  K.truncLEMapOfLE (index_le_succ n)

/-- An upper-truncation transition followed by the later inclusion is the
earlier inclusion. -/
@[reassoc (attr := simp), stacks 06XX]
theorem step_comp_ιTruncLE (K : CochainComplex A ℤ) (n : ℕ) :
    step K n ≫ K.ιTruncLE (index (n + 1)) = K.ιTruncLE (index n) := sorry

/-- 06XX (Lemma 13.29.1): the sequential direct system of canonical upper
truncations of `K`. -/
@[stacks 06XX]
noncomputable def diagram (K : CochainComplex A ℤ) :
    ℕ ⥤ CochainComplex A ℤ :=
  Functor.ofSequence (step K)

/-- The successor map of the upper-truncation diagram is its declared
truncation transition. -/
@[simp, stacks 06XX]
theorem diagram_step (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) = step K n := sorry

/-- 06XX (Lemma 13.29.1): a compatible resolution of the canonical upper
truncation diagram by bounded-above complexes with terms in `P`.

Every stage comparison is a termwise epimorphic quasi-isomorphism, while
successor maps are termwise split monomorphisms with cokernels in `P`. -/
@[stacks 06XX]
structure Resolution (P : ObjectProperty A) (K : CochainComplex A ℤ)
    extends Over (diagram K) where
  /-- The comparison at every stage is a bounded-above termwise-`P`
  quasi-isomorphic epimorphism. -/
  isResolutionStage (n : ℕ) :
    _root_.CochainComplex.Minus.TermsIn.Bounded.QuasiIso.Epi
      P (index n) (stage K n) (left.obj n) (hom.app n)
  /-- Every successor map is split monic in each cochain degree. -/
  termwiseSplitMono (n : ℕ) (i : ℤ) :
    IsSplitMono ((left.map (homOfLE (Nat.le_add_right n 1))).f i)
  /-- Every degreewise cokernel of a successor map belongs to `P`. -/
  cokernel_mem (n : ℕ) (i : ℤ) :
    P (cokernel ((left.map (homOfLE (Nat.le_add_right n 1))).f i))

namespace Resolution

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- The direct system of resolving complexes. -/
abbrev tower (S : Resolution P K) : ℕ ⥤ CochainComplex A ℤ :=
  S.left

/-- The natural comparison from the resolving tower to the canonical
upper-truncation diagram. -/
abbrev comparison (S : Resolution P K) : S.tower ⟶ diagram K :=
  S.hom

/-- The `n`th resolving complex. -/
abbrev stage (S : Resolution P K) (n : ℕ) : CochainComplex A ℤ :=
  S.tower.obj n

/-- The successor map of the resolving tower. -/
abbrev step (S : Resolution P K) (n : ℕ) :
    S.stage n ⟶ S.stage (n + 1) :=
  S.tower.map (homOfLE (Nat.le_add_right n 1))

/-- The map from the `n`th resolving stage to the original complex. -/
@[stacks 06XX]
abbrev toTarget (S : Resolution P K) (n : ℕ) : S.stage n ⟶ K :=
  S.comparison.app n ≫ K.ιTruncLE (index n)

/-- The comparison at stage `n` is a quasi-isomorphism. -/
theorem comparison_quasiIso (S : Resolution P K) (n : ℕ) :
    QuasiIso (S.comparison.app n) := sorry

/-- The resolving complex at stage `n` is zero strictly above its cutoff. -/
theorem stage_isStrictlyLE (S : Resolution P K) (n : ℕ) :
    (S.stage n).IsStrictlyLE (index n) := sorry

/-- Every term of every resolving stage belongs to `P`. -/
theorem stage_term_mem (S : Resolution P K) (n : ℕ) (i : ℤ) :
    P ((S.stage n).X i) := sorry

/-- The comparison at stage `n` is epimorphic. -/
theorem comparison_epi (S : Resolution P K) (n : ℕ) :
    Epi (S.comparison.app n) := sorry

/-- Each successor map is split monic in every degree. -/
theorem step_f_isSplitMono (S : Resolution P K) (n : ℕ) (i : ℤ) :
    IsSplitMono ((S.step n).f i) := sorry

attribute [instance] comparison_quasiIso stage_isStrictlyLE comparison_epi
  step_f_isSplitMono

/-- Every component of a resolution-stage comparison is epimorphic. -/
instance comparison_f_epi (S : Resolution P K) (n : ℕ) (i : ℤ) :
    Epi ((S.comparison.app n).f i) := sorry

/-- Every successor map in a resolving tower is monomorphic. -/
instance step_mono (S : Resolution P K) (n : ℕ) : Mono (S.step n) := sorry

/-- The degreewise cokernel of a successor map belongs to `P`. -/
theorem step_cokernel_mem (S : Resolution P K) (n : ℕ) (i : ℤ) :
    P (cokernel ((S.step n).f i)) := sorry

/-- The chosen comparisons commute with the successor maps of the two
towers. -/
@[reassoc, stacks 06XX]
theorem comparison_naturality (S : Resolution P K) (n : ℕ) :
    S.step n ≫ S.comparison.app (n + 1) =
      S.comparison.app n ≫ UpperTruncation.step K n := sorry

/-- The stage-to-target maps commute with the successor maps. -/
@[reassoc (attr := simp), stacks 06XX]
theorem step_comp_toTarget (S : Resolution P K) (n : ℕ) :
    S.step n ≫ S.toTarget (n + 1) = S.toTarget n := sorry

/-- The full naturality equation used to assemble the canonical cocone. -/
@[stacks 06XX]
theorem toTarget_naturality (S : Resolution P K) (n : ℕ) :
    S.tower.map (homOfLE (Nat.le_add_right n 1)) ≫ S.toTarget (n + 1) =
      S.toTarget n ≫
        ((Functor.const ℕ).obj K).map (homOfLE (Nat.le_add_right n 1)) := sorry

/-- The canonical cocone from an upper-truncation resolution to its target
complex. -/
@[stacks 06XX]
noncomputable def cocone (S : Resolution P K) : Cocone S.tower where
  pt := K
  ι := NatTrans.ofSequence (fun n => S.toTarget n) S.toTarget_naturality

/-- The leg of the canonical resolution cocone is the chosen stage-to-target
map. -/
@[simp, stacks 06XX]
theorem cocone_ι_app (S : Resolution P K) (n : ℕ) :
    S.cocone.ι.app n = S.toTarget n := sorry

/-- The canonical morphism from the colimit of an upper-truncation resolution
to its target complex. -/
@[stacks 06XX]
noncomputable abbrev fromColimit (S : Resolution P K) [HasColimit S.tower] :
    colimit S.tower ⟶ K :=
  colimit.desc S.tower S.cocone

/-- The colimit comparison restricts to the chosen map on every stage. -/
@[reassoc (attr := simp), stacks 06XX]
theorem ι_comp_fromColimit (S : Resolution P K) [HasColimit S.tower] (n : ℕ) :
    colimit.ι S.tower n ≫ S.fromColimit = S.toTarget n := sorry

/-- Maps out of the colimit are equal when they agree on all stage
inclusions. -/
@[stacks 06XX]
theorem hom_ext (S : Resolution P K) [HasColimit S.tower]
    {X : CochainComplex A ℤ} {f g : colimit S.tower ⟶ X}
    (h : ∀ n : ℕ, colimit.ι S.tower n ≫ f = colimit.ι S.tower n ≫ g) :
    f = g := sorry

/-- A map out of the colimit is the canonical comparison when it has the
canonical restriction to every stage. -/
@[stacks 06XX]
theorem eq_fromColimit_of_ι_comp (S : Resolution P K) [HasColimit S.tower]
    {γ : colimit S.tower ⟶ K}
    (hγ : ∀ n : ℕ, colimit.ι S.tower n ≫ γ = S.toTarget n) :
    γ = S.fromColimit := sorry

/-- Characterization of the canonical comparison from the colimit. -/
@[stacks 06XX]
theorem eq_fromColimit_iff (S : Resolution P K) [HasColimit S.tower]
    {γ : colimit S.tower ⟶ K} :
    γ = S.fromColimit ↔
      ∀ n : ℕ, colimit.ι S.tower n ≫ γ = S.toTarget n := sorry

end Resolution

/-- 06XX (Lemma 13.29.1): every cochain complex has an upper-truncation
resolution when `P` contains zero, is closed under finite coproducts, and
admits epimorphic covers. -/
@[stacks 06XX]
theorem exists_resolution (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
    (K : CochainComplex A ℤ) : Nonempty (Resolution P K) := sorry

end CochainComplex.UpperTruncation
