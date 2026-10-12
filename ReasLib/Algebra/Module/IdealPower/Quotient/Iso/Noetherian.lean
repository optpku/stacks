/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.RingTheory.AdicCompletion.Algebra
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
      limitComponent I M N z n := sorry

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
      completionMapFamily I M N z m := sorry

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
    completionMapR I M N z (r • x) = r • completionMapR I M N z x := sorry

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
      limitComponent I M N z n (AdicCompletion.eval I M (n + 1) x) := sorry

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
      completionInvFamily I M N z m := sorry

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
    completionInvR I M N z (r • x) = r • completionInvR I M N z x := sorry

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
        (AdicCompletion.eval I N (n + 1) x) := sorry

/-- The forward completion map followed after its inverse is the identity. -/
@[stacks 09BB "right inverse identity for the completion comparison"]
theorem completionMap_comp_completionInv
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (completionMap I M N z).comp (completionInv I M N z) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I N) := sorry

/-- The inverse completion map followed after the forward map is the identity. -/
@[stacks 09BB "left inverse identity for the completion comparison"]
theorem completionInv_comp_completionMap
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) :
    (completionInv I M N z).comp (completionMap I M N z) =
      LinearMap.id (R := AdicCompletion I R) (M := AdicCompletion I M) := sorry

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
    limitComparison I M N z x = completionMap I M N z x := sorry

/-- Applying the inverse of the canonical comparison uses the inverse completion map. -/
@[simp, stacks 09BB "inverse application of the quotient-equivalence limit comparison"]
theorem limitComparison_symm_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (z : limit (system I M N)) (x : AdicCompletion I N) :
    (limitComparison I M N z).symm x = completionInv I M N z x := sorry

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
    Function.Bijective (limitComparison I M N) := sorry

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
      (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N) := sorry

/-- A stagewise nonempty quotient-equivalence system has a nonempty inverse limit. -/
@[stacks 09BC "compatible family from stagewise ideal-power quotient isomorphisms"]
theorem nonempty_limit_of_stagewise
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N]
    (h : ∀ n : ℕ, Nonempty (stage I M N n)) :
    Nonempty (limit (system I M N)) := sorry

/-- Lemma 15.101.5 (09BC): if `M / I ^ (n + 1) M` and `N / I ^ (n + 1) N` are linearly
isomorphic for every `n`, then the `I`-adic completions of `M` and `N` are linearly isomorphic
over the completed ring. -/
@[stacks 09BC "isomorphic completions from isomorphic ideal-power quotients"]
theorem nonempty_completionEquiv_of_stagewise
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Finite R N]
    (h : ∀ n : ℕ, Nonempty (stage I M N n)) :
    Nonempty (AdicCompletion I M ≃ₗ[AdicCompletion I R] AdicCompletion I N) := sorry

end Ideal.PowerQuotient.Iso
