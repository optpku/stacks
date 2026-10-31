/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom.Noetherian
public import ReasLib.Algebra.Module.IdealPower.Quotient.Iso
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of completions from ideal-power quotients

A compatible point of the inverse system of positive ideal-power quotient equivalences gives
concrete mutually inverse maps on adic completions.  For finite modules over a Noetherian ring,
this system is Mittag-Leffler and the resulting comparison identifies its limit with the type of
linear equivalences between the completions.

@stack 09BB
@stack 09BC
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace Ideal.PowerQuotient.Iso

variable {R : Type u} [CommRing R]

/-- The `n`th quotient equivalence in a compatible point of the equivalence-system limit. -/
@[stacks 09BB "component of a compatible ideal-power quotient equivalence family"]
abbrev limitComponent
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (n : ℕ) : stage I M N n :=
  limit.π (system I M N) (op n) z

/-- Consecutive components of a limit point are related by quotient-equivalence reduction. -/
@[stacks 09BB "compatibility of quotient-equivalence limit components"]
theorem reduce_limitComponent
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (n : ℕ) :
    reduce I M N n (limitComponent I M N z (n + 1)) =
      limitComponent I M N z n := by
  have h := limit.w_apply (system I M N) (homOfLE (Nat.le_add_right n 1)).op z
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h

/-- The quotient-valued family induced in the forward direction by a compatible family of
positive quotient equivalences.  Exponent zero is filled by the unique zero map. -/
@[stacks 09BB "forward quotient family from compatible quotient equivalences"]
noncomputable def completionMapFamily
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (n : ℕ) → AdicCompletion I M →ₗ[R] Ideal.PowerQuotient I N n
  | 0 => 0
  | n + 1 =>
      (limitComponent I M N z n).toLinearMap.comp
        (AdicCompletion.eval I M (n + 1))

/-- The forward quotient-valued family commutes with every ideal-power transition. -/
@[stacks 09BB "compatibility of the forward completion quotient family"]
theorem completionMapFamily_compat
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) {m n : ℕ} (hmn : m ≤ n) :
    (AdicCompletion.transitionMap I N hmn).comp
        (completionMapFamily I M N z n) =
      completionMapFamily I M N z m := by
  refine IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq
    (I := I) (N := (N : Type w)) (a := fun n ↦ n) strictMono_id
    (completionMapFamily I M N z) ?_ hmn
  intro k
  cases k with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
  | succ k =>
      apply LinearMap.ext
      intro x
      change (positiveStep I N k).hom
          (limitComponent I M N z (k + 1) (x.val (k + 1 + 1))) =
        limitComponent I M N z k (x.val (k + 1))
      rw [← reduce_apply, reduce_limitComponent]
      congr 1
      exact x.property (Nat.le_succ (k + 1))

/-- The underlying `R`-linear map on completions induced by a compatible quotient-equivalence
family. -/
@[stacks 09BB "underlying completion map from compatible quotient equivalences"]
noncomputable def completionMapR
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    AdicCompletion I M →ₗ[R] AdicCompletion I N :=
  AdicCompletion.lift I (completionMapFamily I M N z)
    (completionMapFamily_compat I M N z)

/-- The underlying forward map commutes with scalars from the completed ring. -/
@[stacks 09BB "completion-linearity of the forward map"]
theorem completionMapR_map_smul
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (r : AdicCompletion I R)
    (x : AdicCompletion I M) :
    completionMapR I M N z (r • x) = r • completionMapR I M N z x := by
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      change (0 : Ideal.PowerQuotient I N 0) = r.val 0 • 0
      exact (smul_zero _).symm
  | succ n =>
      change limitComponent I M N z n (r.val (n + 1) • x.val (n + 1)) =
        r.val (n + 1) • limitComponent I M N z n (x.val (n + 1))
      induction r.val (n + 1) using Quotient.inductionOn' with
      | _ s => exact map_smul (limitComponent I M N z n) s (x.val (n + 1))

/-- The completion-linear map induced by a compatible family of quotient equivalences. -/
@[stacks 09BB "completion map from compatible quotient equivalences"]
noncomputable def completionMap
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I N where
  __ := completionMapR I M N z
  map_smul' := completionMapR_map_smul I M N z

/-- Evaluation of the forward completion map is the corresponding positive quotient
equivalence. -/
@[stacks 09BB "evaluation of the forward completion map"]
theorem eval_completionMap
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (n : ℕ) (x : AdicCompletion I M) :
    AdicCompletion.eval I N (n + 1) (completionMap I M N z x) =
      limitComponent I M N z n (AdicCompletion.eval I M (n + 1) x) := rfl

/-- The quotient-valued family induced in the reverse direction by a compatible family of
positive quotient equivalences. -/
@[stacks 09BB "inverse quotient family from compatible quotient equivalences"]
noncomputable def completionInvFamily
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (n : ℕ) → AdicCompletion I N →ₗ[R] Ideal.PowerQuotient I M n
  | 0 => 0
  | n + 1 =>
      (limitComponent I M N z n).symm.toLinearMap.comp
        (AdicCompletion.eval I N (n + 1))

/-- The inverse quotient-valued family commutes with every ideal-power transition. -/
@[stacks 09BB "compatibility of the inverse completion quotient family"]
theorem completionInvFamily_compat
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) {m n : ℕ} (hmn : m ≤ n) :
    (AdicCompletion.transitionMap I M hmn).comp
        (completionInvFamily I M N z n) =
      completionInvFamily I M N z m := by
  refine IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq
    (I := I) (N := (M : Type v)) (a := fun n ↦ n) strictMono_id
    (completionInvFamily I M N z) ?_ hmn
  intro k
  cases k with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I M 0) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      apply LinearMap.ext
      intro x
      exact Subsingleton.elim _ _
  | succ k =>
      apply LinearMap.ext
      intro x
      change (positiveStep I M k).hom
          ((limitComponent I M N z (k + 1)).symm (x.val (k + 1 + 1))) =
        (limitComponent I M N z k).symm (x.val (k + 1))
      apply (limitComponent I M N z k).injective
      rw [LinearEquiv.apply_symm_apply, ← reduce_limitComponent I M N z k,
        reduce_apply, LinearEquiv.apply_symm_apply]
      exact x.property (Nat.le_succ (k + 1))

/-- The underlying `R`-linear inverse map on completions induced by a compatible
quotient-equivalence family. -/
@[stacks 09BB "underlying inverse completion map from compatible quotient equivalences"]
noncomputable def completionInvR
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    AdicCompletion I N →ₗ[R] AdicCompletion I M :=
  AdicCompletion.lift I (completionInvFamily I M N z)
    (completionInvFamily_compat I M N z)

/-- The underlying inverse map commutes with scalars from the completed ring. -/
@[stacks 09BB "completion-linearity of the inverse map"]
theorem completionInvR_map_smul
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (r : AdicCompletion I R)
    (x : AdicCompletion I N) :
    completionInvR I M N z (r • x) = r • completionInvR I M N z x := by
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      change (0 : Ideal.PowerQuotient I M 0) = r.val 0 • 0
      exact (smul_zero _).symm
  | succ n =>
      change (limitComponent I M N z n).symm (r.val (n + 1) • x.val (n + 1)) =
        r.val (n + 1) • (limitComponent I M N z n).symm (x.val (n + 1))
      induction r.val (n + 1) using Quotient.inductionOn' with
      | _ s => exact map_smul (limitComponent I M N z n).symm s (x.val (n + 1))

/-- The completion-linear inverse map induced by a compatible family of quotient
equivalences. -/
@[stacks 09BB "inverse completion map from compatible quotient equivalences"]
noncomputable def completionInv
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    AdicCompletion I N →ₗ[AdicCompletion I R] AdicCompletion I M where
  __ := completionInvR I M N z
  map_smul' := completionInvR_map_smul I M N z

/-- Evaluation of the inverse completion map is the inverse positive quotient equivalence. -/
@[stacks 09BB "evaluation of the inverse completion map"]
theorem eval_completionInv
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (n : ℕ) (x : AdicCompletion I N) :
    AdicCompletion.eval I M (n + 1) (completionInv I M N z x) =
      (limitComponent I M N z n).symm
        (AdicCompletion.eval I N (n + 1) x) := rfl

/-- The forward completion map followed after its inverse is the identity. -/
@[stacks 09BB "right inverse identity for the completion comparison"]
theorem completionMap_comp_completionInv
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (completionMap I M N z).comp (completionInv I M N z) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I N) := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I N 0) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      exact Subsingleton.elim _ _
  | succ n =>
      change AdicCompletion.eval I N (n + 1)
          (completionMap I M N z (completionInv I M N z x)) =
        AdicCompletion.eval I N (n + 1) x
      rw [eval_completionMap, eval_completionInv, LinearEquiv.apply_symm_apply]

/-- The inverse completion map followed after the forward map is the identity. -/
@[stacks 09BB "left inverse identity for the completion comparison"]
theorem completionInv_comp_completionMap
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (completionInv I M N z).comp (completionMap I M N z) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := by
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro n
  cases n with
  | zero =>
      haveI : Subsingleton (Ideal.PowerQuotient I M 0) :=
        Submodule.Quotient.subsingleton_iff.mpr (by simp)
      exact Subsingleton.elim _ _
  | succ n =>
      change AdicCompletion.eval I M (n + 1)
          (completionInv I M N z (completionMap I M N z x)) =
        AdicCompletion.eval I M (n + 1) x
      rw [eval_completionInv, eval_completionMap, LinearEquiv.symm_apply_apply]

/-- The canonical comparison sends a compatible family of positive quotient equivalences to
the induced linear equivalence of adic completions. -/
@[stacks 09BB "comparison from compatible quotient equivalences to completion equivalences"]
noncomputable def limitComparison
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    limit (system I M N) →
      (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N) :=
  fun z ↦
    LinearEquiv.ofLinear (completionMap I M N z) (completionInv I M N z)
      (completionMap_comp_completionInv I M N z)
      (completionInv_comp_completionMap I M N z)

/-- Applying the canonical comparison uses the forward completion map. -/
@[simp, stacks 09BB "application of the quotient-equivalence limit comparison"]
theorem limitComparison_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (x : AdicCompletion I M) :
    limitComparison I M N z x = completionMap I M N z x := rfl

/-- Applying the inverse of the canonical comparison uses the inverse completion map. -/
@[simp, stacks 09BB "inverse application of the quotient-equivalence limit comparison"]
theorem limitComparison_symm_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (x : AdicCompletion I N) :
    (limitComparison I M N z).symm x = completionInv I M N z x := rfl

variable [IsNoetherianRing R]

/-- Lemma 15.101.4 (1) (09BB): for finite modules over a Noetherian ring, the inverse system
of equivalences between their positive ideal-power quotient stages is Mittag-Leffler. -/
@[stacks 09BB "Mittag-Leffler property for isomorphisms over ideal-power quotients"]
theorem system_isMittagLeffler
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] :
    (system I M N).IsMittagLeffler := sorry

/-- Lemma 15.101.4 (4) (09BB): for finite modules over a Noetherian ring, the canonical comparison from compatible
quotient equivalences to completion equivalences is bijective. -/
@[stacks 09BB "bijectivity of the quotient-equivalence limit comparison"]
theorem limitComparison_bijective
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] :
    Function.Bijective (limitComparison I M N) := by
  classical
  constructor
  · intro z z' h
    apply Types.limit_ext (system I M N)
    intro ⟨n⟩
    apply LinearEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := AdicCompletion.eval_surjective I M (n + 1) q
    have hx := congrArg (fun e : AdicCompletion I M ≃ₗ[AdicCompletion I R]
        AdicCompletion I N ↦ AdicCompletion.eval I N (n + 1) (e x)) h
    simpa only [limitComparison_apply, eval_completionMap] using hx
  · intro f
    let qM (n : ℕ) :
        (AdicCompletion I M ⧸ (I ^ (n + 1) • ⊤ : Submodule R (AdicCompletion I M)))
          ≃ₗ[R] positiveStage I M n :=
      (Submodule.quotEquivOfEq _ _
        (AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing)).trans
          ((AdicCompletion.eval I M (n + 1)).quotKerEquivOfSurjective
            (AdicCompletion.eval_surjective I M (n + 1)))
    let qN (n : ℕ) :
        (AdicCompletion I N ⧸ (I ^ (n + 1) • ⊤ : Submodule R (AdicCompletion I N)))
          ≃ₗ[R] positiveStage I N n :=
      (Submodule.quotEquivOfEq _ _
        (AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing)).trans
          ((AdicCompletion.eval I N (n + 1)).quotKerEquivOfSurjective
            (AdicCompletion.eval_surjective I N (n + 1)))
    let e (n : ℕ) : stage I M N n :=
      (qM n).symm.trans
        ((Submodule.Quotient.equiv
          (I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I M)))
          (I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I N)))
          (f.restrictScalars R) (by
            rw [Submodule.map_smul'', Submodule.map_top,
              LinearMap.range_eq_top.mpr (f.restrictScalars R).surjective])).trans (qN n))
    have hM (n : ℕ) (x : AdicCompletion I M) :
        qM n (Submodule.Quotient.mk x) = AdicCompletion.eval I M (n + 1) x := by
      simp [qM]
    have hN (n : ℕ) (x : AdicCompletion I N) :
        qN n (Submodule.Quotient.mk x) = AdicCompletion.eval I N (n + 1) x := by
      simp [qN]
    have he (n : ℕ) (x : AdicCompletion I M) :
        e n (AdicCompletion.eval I M (n + 1) x) =
          AdicCompletion.eval I N (n + 1) (f x) := by
      dsimp only [e, LinearEquiv.trans_apply]
      rw [← hM n x, LinearEquiv.symm_apply_apply]
      change qN n (Submodule.Quotient.mk (f x)) = _
      exact hN n (f x)
    have hstep (n : ℕ) : reduce I M N n (e (n + 1)) = e n := by
      apply LinearEquiv.ext
      intro q
      obtain ⟨x, rfl⟩ := AdicCompletion.eval_surjective I M (n + 1) q
      change reduce I M N n (e (n + 1)) (x.val (n + 1)) = e n (x.val (n + 1))
      calc
        _ = reduce I M N n (e (n + 1))
            ((positiveStep I M n).hom (x.val (n + 1 + 1))) := by
              congr 1
              exact (x.property (Nat.le_succ (n + 1))).symm
        _ = (positiveStep I N n).hom (e (n + 1) (x.val (n + 1 + 1))) :=
          reduce_apply I M N n (e (n + 1)) _
        _ = (positiveStep I N n).hom ((f x).val (n + 1 + 1)) :=
          congrArg (positiveStep I N n).hom (he (n + 1) x)
        _ = (f x).val (n + 1) := (f x).property (Nat.le_succ (n + 1))
        _ = e n (x.val (n + 1)) := (he n x).symm
    have hcompat {m n : ℕ} (hmn : m ≤ n) :
        (system I M N).map (homOfLE hmn).op (e n) = e m := by
      induction n, hmn using Nat.le_induction with
      | base =>
          rw [show (homOfLE (le_refl m)).op = 𝟙 (op m) from Subsingleton.elim _ _,
            CategoryTheory.Functor.map_id]
          rfl
      | succ n hmn ih =>
          have hcomp : (homOfLE (Nat.le_succ_of_le hmn)).op =
              (homOfLE (Nat.le_succ n)).op ≫ (homOfLE hmn).op := Subsingleton.elim _ _
          rw [hcomp, CategoryTheory.Functor.map_comp,
            CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ]
          change (system I M N).map (homOfLE hmn).op (reduce I M N n (e (n + 1))) = e m
          rw [hstep]
          exact ih
    let z := Types.Limit.mk (system I M N) (fun j ↦ e j.unop)
      (fun i j g ↦ by
        have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
        rw [hg]
        exact hcompat (leOfHom g.unop))
    refine ⟨z, ?_⟩
    apply LinearEquiv.ext
    intro x
    apply AdicCompletion.ext
    intro n
    cases n with
    | zero =>
        haveI : Subsingleton (Ideal.PowerQuotient I N 0) :=
          Submodule.Quotient.subsingleton_iff.mpr (by simp)
        exact Subsingleton.elim _ _
    | succ n =>
        change limitComponent I M N z n (x.val (n + 1)) = (f x).val (n + 1)
        have hz : limitComponent I M N z n = e n := by
          dsimp only [limitComponent, z]
          exact Types.Limit.π_mk _ _ _ _
        rw [hz]
        exact he n x

/-- Lemma 15.101.4 (4) (09BB): the limit of the positive quotient-equivalence system is
isomorphic to the type of linear equivalences between the adic completions.  The canonical
forward map is `limitComparison`, whose bijectivity is exposed separately. -/
@[stacks 09BB "limit of isomorphisms over ideal-power quotients"]
theorem limit_isIsomorphic_completionEquiv
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N] :
    IsIsomorphic
      (limit (system I M N))
      (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N) := by
  exact ⟨(Equiv.ofBijective (limitComparison I M N)
    (limitComparison_bijective I M N)).toIso⟩

/-- A stagewise nonempty quotient-equivalence system has a nonempty inverse limit. -/
@[stacks 09BC "compatible family from stagewise ideal-power quotient isomorphisms"]
theorem nonempty_limit_of_stagewise
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N]
    (h : ∀ n : ℕ, Nonempty (stage I M N n)) :
    Nonempty (limit (system I M N)) := by
  classical
  let F := system I M N
  have image_range {A B : Type (max v w)} (f : A ⟶ B) :
      Set.range (imageSubobject f).arrow = Set.range f := by
    have hs : Function.Surjective (factorThruImageSubobject f) :=
      (epi_iff_surjective _).mp inferInstance
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hs x
      exact ⟨a, (ConcreteCategory.congr_hom (imageSubobject_arrow_comp f) a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨factorThruImageSubobject f a,
        ConcreteCategory.congr_hom (imageSubobject_arrow_comp f) a⟩
  have hF : Functor.IsMittagLeffler F := by
    intro j
    obtain ⟨c, hjc, hc⟩ := system_isMittagLeffler I M N j.unop
    refine ⟨op c, (homOfLE hjc).op, ?_⟩
    intro k g y hy
    have hr := congrArg (fun s : Subobject (F.obj j) ↦ Set.range s.arrow)
      (hc (le_max_left c k.unop))
    rw [image_range, image_range] at hr
    rw [← hr] at hy
    obtain ⟨a, rfl⟩ := hy
    refine ⟨F.map (homOfLE (le_max_right c k.unop)).op a, ?_⟩
    change F.map g (F.map (homOfLE (le_max_right c k.unop)).op a) =
      F.map (homOfLE (hjc.trans (le_max_left c k.unop))).op a
    have hcomp :
        (homOfLE (hjc.trans (le_max_left c k.unop))).op =
          (homOfLE (le_max_right c k.unop)).op ≫ g := Subsingleton.elim _ _
    rw [hcomp, Functor.map_comp]
    rfl
  letI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j ↦ h j.unop
  let E := F.toEventualRanges
  obtain ⟨x⟩ := F.toEventualRanges_nonempty hF (op 0)
  obtain ⟨z, _⟩ := Types.surjective_π_app_zero_of_surjective_map (limit.isLimit E)
    (fun n ↦ F.surjective_toEventualRanges hF (homOfLE (Nat.le_succ n)).op) x
  exact ⟨(Types.limitEquivSections F).symm
    (F.toEventualRangesSectionsEquiv (Types.limitEquivSections E z))⟩

/-- Lemma 15.101.5 (09BC): if `M / I ^ (n + 1) M` and `N / I ^ (n + 1) N` are linearly
isomorphic for every `n`, then the `I`-adic completions of `M` and `N` are linearly isomorphic
over the completed ring. -/
@[stacks 09BC "isomorphic completions from isomorphic ideal-power quotients"]
theorem nonempty_completionEquiv_of_stagewise
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N]
    (h : ∀ n : ℕ, Nonempty (stage I M N n)) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N) := by
  exact (nonempty_limit_of_stagewise I M N h).map (limitComparison I M N)

end Ideal.PowerQuotient.Iso
