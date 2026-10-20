/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Quotient
public import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom systems over ideal-power quotients

@stack 09BB
@stack 0EGY

This file owns the sequential inverse systems

`n ↦ Hom_R(M, N / I ^ (n + 1) N)`

and the source-facing system
`n ↦ Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)`,
with a natural isomorphism between them.  It also owns the canonical comparison from the
positive ideal-power quotient system of
`Hom_R(M, N)`.  The quotient carriers and their transitions come from
`Ideal.PowerQuotient`; this leaf only adds the functorial Hom layer.
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped ModuleCat.Algebra

noncomputable section

universe u v w

namespace Ideal.PowerQuotient.Hom

variable {R : Type u} [CommRing R]

/-! ### Universal property over the quotient ring -/

/-- An `R / I ^ n`-module regarded canonically as an `R`-module. -/
@[stacks 0EGY "base restriction of an exact quotient-ring module"]
def overBase (I : Ideal R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) : ModuleCat.{v} R :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj P

/-- Base-linear maps from `M` to a module over `R / I ^ n`, with the target scalars restricted
along the quotient map. -/
@[stacks 0EGY "base-linear maps into an exact quotient-ring module"]
abbrev baseHom (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) : Type v :=
  M ⟶ overBase I P

/-- Every base-linear map into an `R / I ^ n`-module kills `I ^ n M`. -/
@[stacks 0EGY "kernel bound for maps into an exact quotient-ring module"]
theorem power_smul_le_ker (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) :
    I ^ n • (⊤ : Submodule R (M : Type v)) ≤ LinearMap.ker f.hom := sorry

/-- Descend a base-linear map `M ⟶ P` to an `R / I ^ n`-linear morphism
`M / I ^ n M ⟶ P`.  The quotient-ring linearity is recovered by full faithfulness of
restriction along the surjective quotient map. -/
@[stacks 0EGY "descent to an exact quotient-ring module"]
noncomputable def lift (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) :
    stageOver I M n ⟶ P :=
  ModuleCat.RestrictScalars.Surjective.preimage
    (Ideal.Quotient.mk (I ^ n)) Ideal.Quotient.mk_surjective
    ((stageIsoRestricted I M n).inv ≫
      ModuleCat.ofHom (X := stage I M n) (Y := overBase I P)
        ((@Submodule.liftQ R (M : Type v) inferInstance M.isAddCommGroup M.isModule
          (I ^ n • (⊤ : Submodule R (M : Type v))) R (overBase I P : Type v)
          inferInstance (overBase I P).isAddCommGroup (overBase I P).isModule
          (RingHom.id R) f.hom (power_smul_le_ker I M P f)) :
            (stage I M n : Type v) →ₗ[R] (overBase I P : Type v)))

/-- Quotient-ring descent has the prescribed value on quotient representatives. -/
@[simp, stacks 0EGY "quotient-ring descent on representatives"]
theorem lift_mk (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) (x : M) :
    (lift I M P f).hom (Ideal.PowerQuotient.mk I M n x) = f.hom x := sorry

/-- Quotient-ring descent preserves addition. -/
@[stacks 0EGY "additivity of quotient-ring descent"]
theorem lift_add (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f g : baseHom I M P) :
    lift I M P (f + g) = lift I M P f + lift I M P g := sorry

/-- Quotient-ring descent respects the original-ring scalar action. -/
@[stacks 0EGY "linearity of quotient-ring descent over the base ring"]
theorem lift_smul (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (r : R) (f : baseHom I M P) :
    lift I M P (r • f) = r • lift I M P f := sorry

/-- Restrict a quotient-ring morphism along `M ⟶ M / I ^ n M` and the quotient map
`R ⟶ R / I ^ n`. -/
@[stacks 0EGY "restriction from an exact quotient-ring Hom"]
abbrev restrict (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (g : stageOver I M n ⟶ P) :
    baseHom I M P :=
  (ModuleCat.ofHom (Ideal.PowerQuotient.mk I M n) : M ⟶ restrictedStage I M n) ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map g

/-- Restriction from quotient-ring morphisms preserves addition. -/
@[stacks 0EGY "additivity of restriction from quotient-ring morphisms"]
theorem restrict_add (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f g : stageOver I M n ⟶ P) :
    restrict I M P (f + g) = restrict I M P f + restrict I M P g := sorry

/-- Restriction from quotient-ring morphisms respects the original-ring scalar action. -/
@[stacks 0EGY "linearity of restriction from quotient-ring morphisms"]
theorem restrict_smul (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (r : R) (g : stageOver I M n ⟶ P) :
    restrict I M P (r • g) = r • restrict I M P g := sorry

/-- Descending after restriction is the identity on quotient-ring morphisms. -/
@[simp, stacks 0EGY "descent-restriction inverse law for quotient-ring morphisms"]
theorem lift_restrict (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (g : stageOver I M n ⟶ P) :
    lift I M P (restrict I M P g) = g := sorry

/-- Restricting after descent is the identity on base-linear maps. -/
@[simp, stacks 0EGY "restriction-descent inverse law for quotient-ring morphisms"]
theorem restrict_lift (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) :
    restrict I M P (lift I M P f) = f := sorry

/-- Base-linear maps into an `R / I ^ n`-module are canonically equivalent to quotient-ring
linear morphisms out of `M / I ^ n M`. -/
@[stacks 0EGY "universal Hom equivalence for an exact quotient-ring module"]
noncomputable def equiv (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) :
    baseHom I M P ≃+ (stageOver I M n ⟶ P) where
  toFun := lift I M P
  invFun := restrict I M P
  left_inv f := restrict_lift I M P f
  right_inv g := lift_restrict I M P g
  map_add' := lift_add I M P

/-- The forward map of `equiv` is explicit quotient-ring descent. -/
@[simp, stacks 0EGY "forward map of the quotient-ring Hom equivalence"]
theorem equiv_apply (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) :
    equiv I M P f = lift I M P f := sorry

/-- The inverse map of `equiv` is restriction along the quotient maps. -/
@[simp, stacks 0EGY "inverse map of the quotient-ring Hom equivalence"]
theorem equiv_symm_apply (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (g : stageOver I M n ⟶ P) :
    (equiv I M P).symm g = restrict I M P g := sorry

/-- The universal Hom equivalence is linear over the original commutative ring. -/
@[stacks 0EGY "linear universal Hom equivalence for an exact quotient-ring module"]
noncomputable def linearEquiv (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) :
    baseHom I M P ≃ₗ[R] (stageOver I M n ⟶ P) :=
  { __ := equiv I M P
    map_smul' := lift_smul I M P }

/-- The forward map of the linear universal Hom equivalence is quotient descent. -/
@[simp, stacks 0EGY "forward map of the linear quotient-ring Hom equivalence"]
theorem linearEquiv_apply (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (f : baseHom I M P) :
    linearEquiv I M P f = lift I M P f := sorry

/-- The inverse of the linear universal Hom equivalence is restriction along the quotient maps. -/
@[simp, stacks 0EGY "inverse map of the linear quotient-ring Hom equivalence"]
theorem linearEquiv_symm_apply (I : Ideal R) (M : ModuleCat.{v} R) {n : ℕ}
    (P : ModuleCat.{v} (R ⧸ I ^ n)) (g : stageOver I M n ⟶ P) :
    (linearEquiv I M P).symm g = restrict I M P g := sorry

/-- The stage `Hom_R(M, N / I ^ (n + 1) N)` of the positive ideal-power Hom system. -/
@[stacks 09BB "Hom stage over a positive ideal-power quotient"]
abbrev stage
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) : Type (max v w) :=
  M →ₗ[R] positive I N n

/-- The source-facing stage
`Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)` from Lemma 15.101.4. -/
@[stacks 09BB "Hom between positive ideal-power quotient stages"]
abbrev quotientStage
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) : Type (max v w) :=
  positive I M n →ₗ[R] positive I N n

/-! ### Exact positive-indexed stages -/

/-- The exact positive stage `Hom_R(M, N / I ^ n N)`, indexed directly by `n : ℕ+`. -/
@[stacks 09BB "Hom stage over an exact positive ideal power"]
abbrev exactStage
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : Type (max v w) :=
  M →ₗ[R] Ideal.PowerQuotient I N (n : ℕ)

/-- The exact positive stage
`Hom_R(M / I ^ n M, N / I ^ n N)`, indexed directly by `n : ℕ+`. -/
@[stacks 09BB "Hom between exact positive ideal-power quotient stages"]
abbrev exactQuotientStage
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : Type (max v w) :=
  Ideal.PowerQuotient I M (n : ℕ) →ₗ[R] Ideal.PowerQuotient I N (n : ℕ)

/-- Precomposition with the exact quotient map restricts a map between exact quotient stages to
the original source module. -/
@[stacks 09BB "restriction from exact quotient-stage Hom"]
abbrev exactRestrictDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : exactQuotientStage I M N n →ₗ[R] exactStage I M N n :=
  LinearMap.lcomp R (Ideal.PowerQuotient I N (n : ℕ))
    (Ideal.PowerQuotient.mk I (ModuleCat.of R M) (n : ℕ))

/-- Exact restriction evaluates a quotient-stage map on the canonical class of a source
element. -/
@[simp, stacks 09BB "pointwise restriction from exact quotient-stage Hom"]
theorem exactRestrictDomain_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) (f : exactQuotientStage I M N n) (x : M) :
    exactRestrictDomain I M N n f x = f (Submodule.Quotient.mk x) := sorry

/-- Every map into `N / I ^ n N` kills `I ^ n M`. -/
@[stacks 09BB "factorization condition at an exact positive ideal power"]
theorem exactPow_smul_le_ker
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) (f : exactStage I M N n) :
    I ^ (n : ℕ) • (⊤ : Submodule R M) ≤ LinearMap.ker f := sorry

/-- The linear operation factoring a map through the exact quotient `M / I ^ n M`. -/
@[stacks 09BB "factorization through an exact positive source quotient"]
noncomputable def exactLiftDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : exactStage I M N n →ₗ[R] exactQuotientStage I M N n where
  toFun f := Submodule.liftQ
    (I ^ (n : ℕ) • (⊤ : Submodule R M)) f
    (exactPow_smul_le_ker I M N n f)
  map_add' := sorry
  map_smul' := sorry

/-- The exact positive-stage equivalence
`Hom_R(M / I ^ n M, N / I ^ n N) ≃ Hom_R(M, N / I ^ n N)`. -/
@[stacks 09BB "exact quotient-domain Hom equivalence"]
noncomputable def exactStageEquiv
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : exactQuotientStage I M N n ≃ₗ[R] exactStage I M N n :=
  LinearEquiv.ofLinear (exactRestrictDomain I M N n) (exactLiftDomain I M N n) sorry sorry

/-- Exact source-quotient factorization has the expected value on representatives. -/
@[simp, stacks 09BB "exact source-quotient Hom factorization on representatives"]
theorem exactLiftDomain_mk
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) (f : exactStage I M N n) (x : M) :
    exactLiftDomain I M N n f (Submodule.Quotient.mk x) = f x := sorry

/-- The forward map of `exactStageEquiv` is precomposition with the exact quotient map. -/
@[simp, stacks 09BB "application of the exact quotient-domain Hom equivalence"]
theorem exactStageEquiv_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) (f : exactQuotientStage I M N n) :
    exactStageEquiv I M N n f = exactRestrictDomain I M N n f := sorry

/-- The inverse map of `exactStageEquiv` is the explicit quotient factorization map. -/
@[simp, stacks 09BB "inverse of the exact quotient-domain Hom equivalence"]
theorem exactStageEquiv_symm_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) (f : exactStage I M N n) :
    (exactStageEquiv I M N n).symm f = exactLiftDomain I M N n f := sorry

/-- Pointwise reduction sends a linear map `M →ₗ[R] N` to a map
`M →ₗ[R] N / I ^ n N`. -/
@[stacks 09BB "pointwise reduction at an exact positive ideal power"]
noncomputable def exactReduction
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) : (M →ₗ[R] N) →ₗ[R] exactStage I M N n where
  toFun f := (Ideal.PowerQuotient.mk I (ModuleCat.of R N) (n : ℕ)).comp f
  map_add' := sorry
  map_smul' := sorry

/-- The canonical comparison from the exact quotient of `Hom_R(M, N)` to maps from `M` into
`N / I ^ n N`. -/
@[stacks 09BB "comparison from an exact Hom quotient"]
noncomputable def exactComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) :
    Ideal.PowerQuotient I (M →ₗ[R] N) (n : ℕ) →ₗ[R] exactStage I M N n :=
  Submodule.liftQ
    (I ^ (n : ℕ) • (⊤ : Submodule R (M →ₗ[R] N)))
    (exactReduction I M N n) sorry

/-- The canonical comparison from the exact quotient of `Hom_R(M, N)` to maps between the exact
quotient stages of `M` and `N`. -/
@[stacks 09BB "comparison into exact quotient-stage Hom"]
noncomputable def exactQuotientComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ+) :
    Ideal.PowerQuotient I (M →ₗ[R] N) (n : ℕ) →ₗ[R]
      exactQuotientStage I M N n :=
  (exactLiftDomain I M N n).comp (exactComparison I M N n)

/-- Precomposition with the quotient map turns a map between quotient stages into a map from the
original source module. -/
@[stacks 09BB "restriction from quotient-stage Hom to the canonical Hom model"]
abbrev restrictDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) : quotientStage I M N n →ₗ[R] stage I M N n :=
  LinearMap.lcomp R (positive I N n)
    (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M)))

/-- Precomposition with `restrictDomain` evaluates a quotient-stage map on the canonical quotient
class of a source element. -/
@[simp, stacks 09BB "pointwise restriction from quotient-stage Hom"]
theorem restrictDomain_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : quotientStage I M N n) (x : M) :
    restrictDomain I M N n f x = f (Submodule.Quotient.mk x) := sorry

/-- Every map into `N / I ^ (n + 1) N` kills `I ^ (n + 1) M`. -/
@[stacks 09BB "factorization condition for quotienting the Hom source"]
theorem pow_smul_le_ker_stage
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : stage I M N n) :
    I ^ (n + 1) • (⊤ : Submodule R M) ≤ LinearMap.ker f := sorry

/-- Factoring maps through the source quotient is additive. -/
@[stacks 09BB "additivity of source-quotient factorization"]
theorem liftDomain_add
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f g : stage I M N n) :
    Submodule.liftQ
        (I ^ (n + 1) • (⊤ : Submodule R M)) (f + g)
        (pow_smul_le_ker_stage I M N n (f + g)) =
      Submodule.liftQ
          (I ^ (n + 1) • (⊤ : Submodule R M)) f
          (pow_smul_le_ker_stage I M N n f) +
        Submodule.liftQ
          (I ^ (n + 1) • (⊤ : Submodule R M)) g
          (pow_smul_le_ker_stage I M N n g) := sorry

/-- Factoring maps through the source quotient is compatible with scalar multiplication. -/
@[stacks 09BB "linearity of source-quotient factorization"]
theorem liftDomain_smul
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (r : R) (f : stage I M N n) :
    Submodule.liftQ
        (I ^ (n + 1) • (⊤ : Submodule R M)) (r • f)
        (pow_smul_le_ker_stage I M N n (r • f)) =
      r • Submodule.liftQ
        (I ^ (n + 1) • (⊤ : Submodule R M)) f
        (pow_smul_le_ker_stage I M N n f) := sorry

/-- The linear operation that factors a map through `M / I ^ (n + 1) M`. -/
@[stacks 09BB "factorization through the positive ideal-power source quotient"]
noncomputable def liftDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) : stage I M N n →ₗ[R] quotientStage I M N n where
  toFun f := Submodule.liftQ
    (I ^ (n + 1) • (⊤ : Submodule R M)) f
    (pow_smul_le_ker_stage I M N n f)
  map_add' := liftDomain_add I M N n
  map_smul' := liftDomain_smul I M N n

/-- Factoring a map through the source quotient has the expected representative formula. -/
@[simp, stacks 09BB "pointwise source-quotient Hom factorization"]
theorem liftDomain_mk
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : stage I M N n) (x : M) :
    liftDomain I M N n f (Submodule.Quotient.mk x) = f x := sorry

/-- Restricting after source-quotient factorization is the identity. -/
@[stacks 09BB "source-quotient Hom factorization inverse law"]
theorem restrictDomain_comp_liftDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (restrictDomain I M N n).comp (liftDomain I M N n) = LinearMap.id := sorry

/-- Factoring after restriction along the source quotient is the identity. -/
@[stacks 09BB "quotient-stage Hom restriction inverse law"]
theorem liftDomain_comp_restrictDomain
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (liftDomain I M N n).comp (restrictDomain I M N n) = LinearMap.id := sorry

/-- The canonical equivalence
`Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N) ≃ Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "quotient-domain model for the positive ideal-power Hom stage"]
noncomputable def quotientStageEquiv
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) : quotientStage I M N n ≃ₗ[R] stage I M N n :=
  LinearEquiv.ofLinear (restrictDomain I M N n) (liftDomain I M N n)
    (restrictDomain_comp_liftDomain I M N n)
    (liftDomain_comp_restrictDomain I M N n)

/-- The quotient-stage Hom equivalence is precomposition with the source quotient map. -/
@[simp, stacks 09BB "application of the quotient-domain Hom equivalence"]
theorem quotientStageEquiv_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : quotientStage I M N n) :
    quotientStageEquiv I M N n f = restrictDomain I M N n f := sorry

/-- The inverse of `quotientStageEquiv` is the explicit quotient factorization map. -/
@[simp, stacks 09BB "inverse of the quotient-domain Hom equivalence"]
theorem quotientStageEquiv_symm_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : stage I M N n) :
    (quotientStageEquiv I M N n).symm f = liftDomain I M N n f := sorry

/-- Postcomposition with quotient reduction gives the successor transition on the Hom stages. -/
@[stacks 09BB "transition on the positive ideal-power Hom system"]
abbrev step
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    stage I M N (n + 1) →ₗ[R] stage I M N n :=
  LinearMap.compRight R (positiveStep I (ModuleCat.of R N) n).hom

/-- The sequential inverse system `n ↦ Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "positive ideal-power Hom inverse system"]
abbrev system
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    SequentialInverseSystem (ModuleCat.{max v w} R) :=
  @Functor.ofOpSequence (ModuleCat.{max v w} R) _
    (fun n ↦ ModuleCat.of R (stage I M N n))
    (fun n ↦ ModuleCat.ofHom (step I M N n))

/-- The transition on the source-facing stages
`Hom_R(M / I ^ (n + 2) M, N / I ^ (n + 2) N)`.  It is transported from the
smaller canonical Hom model through `quotientStageEquiv`. -/
@[stacks 09BB "transition on Hom between positive ideal-power quotients"]
noncomputable def quotientStep
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    quotientStage I M N (n + 1) →ₗ[R] quotientStage I M N n :=
  (quotientStageEquiv I M N n).symm.toLinearMap.comp
    ((step I M N n).comp (quotientStageEquiv I M N (n + 1)).toLinearMap)

/-- The sequential inverse system
`n ↦ Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)` appearing in Lemma 15.101.4. -/
@[stacks 09BB "Hom system between positive ideal-power quotients"]
noncomputable def quotientSystem
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    SequentialInverseSystem (ModuleCat.{max v w} R) :=
  @Functor.ofOpSequence (ModuleCat.{max v w} R) _
    (fun n ↦ ModuleCat.of R (quotientStage I M N n))
    (fun n ↦ ModuleCat.ofHom (quotientStep I M N n))

/-- The quotient-domain transition corresponds to postcomposition in the canonical Hom model. -/
@[stacks 09BB "compatibility of quotient-domain Hom transitions"]
theorem quotientStageEquiv_quotientStep
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : quotientStage I M N (n + 1)) :
    quotientStageEquiv I M N n (quotientStep I M N n f) =
      step I M N n (quotientStageEquiv I M N (n + 1) f) := sorry

/-- The stage equivalences between the source-facing and canonical Hom models are natural in the
inverse-system index. -/
@[stacks 09BB "naturality of the quotient-domain Hom model"]
theorem quotientSystemIso_naturality
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (quotientSystem I M N).map f ≫
        (quotientStageEquiv I M N j.unop).toModuleIso.hom =
      (quotientStageEquiv I M N i.unop).toModuleIso.hom ≫
        (system I M N).map f := sorry

/-- The source-facing system of maps between quotient stages is naturally isomorphic to the
canonical system `n ↦ Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "quotient-domain model of the positive ideal-power Hom system"]
noncomputable def quotientSystemIso
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    quotientSystem I M N ≅ system I M N :=
  NatIso.ofComponents
    (fun n ↦ (quotientStageEquiv I M N n.unop).toModuleIso)
    (quotientSystemIso_naturality I M N)

/-- The forward component of `quotientSystemIso` is the quotient-domain stage equivalence. -/
@[simp, stacks 09BB "component of the quotient-domain Hom system isomorphism"]
theorem quotientSystemIso_hom_app
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientSystemIso I M N).hom.app (op n) =
      (quotientStageEquiv I M N n).toModuleIso.hom := sorry

/-- The inverse component of `quotientSystemIso` is quotient factorization in the source. -/
@[simp, stacks 09BB "inverse component of the quotient-domain Hom system isomorphism"]
theorem quotientSystemIso_inv_app
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientSystemIso I M N).inv.app (op n) =
      (quotientStageEquiv I M N n).toModuleIso.inv := sorry

/-- Applying the Hom transition reduces the value of a map by one ideal-power stage. -/
@[simp, stacks 09BB "application of the positive ideal-power Hom transition"]
theorem step_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : stage I M N (n + 1)) (x : M) :
    step I M N n f x = (positiveStep I (ModuleCat.of R N) n).hom (f x) := sorry

/-- The object at index `n` in the Hom system is its explicit stage. -/
@[simp, stacks 09BB "object of the positive ideal-power Hom system"]
theorem system_obj
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (system I M N).obj (op n) = ModuleCat.of R (stage I M N n) := sorry

/-- The successor map of the Hom system is the explicit postcomposition transition. -/
@[simp, stacks 09BB "successor map of the positive ideal-power Hom system"]
theorem system_stepMap
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (system I M N).stepMap n = ModuleCat.ofHom (step I M N n) := sorry

/-- The object at index `n` in the source-facing Hom system is the explicit quotient-domain
stage. -/
@[simp, stacks 09BB "object of the quotient-domain Hom system"]
theorem quotientSystem_obj
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientSystem I M N).obj (op n) =
      ModuleCat.of R (quotientStage I M N n) := sorry

/-- The successor map of the source-facing Hom system is `quotientStep`. -/
@[simp, stacks 09BB "successor map of the quotient-domain Hom system"]
theorem quotientSystem_stepMap
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientSystem I M N).stepMap n = ModuleCat.ofHom (quotientStep I M N n) := sorry

/-- The canonical map `Hom_R(M, N) → Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "reduction into a positive ideal-power Hom stage"]
abbrev reduction
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (M →ₗ[R] N) →ₗ[R] stage I M N n :=
  LinearMap.compRight R
    (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R N)))

/-- Reduction sends a map to its pointwise quotient class. -/
@[simp, stacks 09BB "pointwise formula for reduction into a Hom stage"]
theorem reduction_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) (x : M) :
    reduction I M N n f x =
      (Submodule.Quotient.mk (f x) : positive I N n) := sorry

/-- Reduction to consecutive Hom stages commutes with the successor transition. -/
@[stacks 09BB "successor compatibility of reduction into Hom stages"]
theorem reduction_step
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (step I M N n).comp (reduction I M N (n + 1)) =
      reduction I M N n := sorry

/-- The submodule `I ^ (n + 1) Hom_R(M, N)` lies in the kernel of pointwise reduction. -/
@[stacks 09BB "kernel condition for the quotient Hom comparison"]
theorem pow_smul_le_ker_reduction
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule R (M →ₗ[R] N)) ≤
      LinearMap.ker (reduction I M N n) := sorry

/-- The canonical comparison
`Hom_R(M, N) / I ^ (n + 1) Hom_R(M, N) → Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "comparison from the quotient of Hom to Hom of the quotient"]
noncomputable def comparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    positive I (M →ₗ[R] N) n →ₗ[R] stage I M N n :=
  Submodule.liftQ
    (I ^ (n + 1) • (⊤ : Submodule R (M →ₗ[R] N)))
    (reduction I M N n)
    (pow_smul_le_ker_reduction I M N n)

/-- The quotient-Hom comparison sends the class of `f` to its pointwise reduction. -/
@[simp, stacks 09BB "quotient Hom comparison on representatives"]
theorem comparison_mk
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) :
    comparison I M N n
        (Submodule.Quotient.mk f : positive I (M →ₗ[R] N) n) =
      reduction I M N n f := sorry

/-- Pointwise, the quotient-Hom comparison sends `[f]` to `x ↦ [f x]`. -/
@[simp, stacks 09BB "pointwise quotient Hom comparison on representatives"]
theorem comparison_mk_apply
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) (x : M) :
    comparison I M N n
        (Submodule.Quotient.mk f : positive I (M →ₗ[R] N) n) x =
      (Submodule.Quotient.mk (f x) : positive I N n) := sorry

/-- The quotient-Hom comparisons commute with the successor transitions. -/
@[stacks 09BB "successor compatibility of the quotient Hom comparison"]
theorem comparison_step
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (comparison I M N n).comp
        (positiveStep I (ModuleCat.of R (M →ₗ[R] N)) n).hom =
      (step I M N n).comp (comparison I M N (n + 1)) := sorry

/-- The quotient-Hom comparison with the source-facing target
`Hom_R(M / I ^ (n + 1) M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "comparison into Hom between quotient stages"]
noncomputable def quotientComparison
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    positive I (M →ₗ[R] N) n →ₗ[R] quotientStage I M N n :=
  (quotientStageEquiv I M N n).symm.toLinearMap.comp (comparison I M N n)

/-- The source-facing quotient-Hom comparison sends a representative to the map induced on
quotient modules. -/
@[simp, stacks 09BB "quotient-domain comparison on representatives"]
theorem quotientComparison_mk
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) :
    quotientComparison I M N n
        (Submodule.Quotient.mk f : positive I (M →ₗ[R] N) n) =
      (quotientStageEquiv I M N n).symm (reduction I M N n f) := sorry

/-- The source-facing quotient-Hom comparisons commute with quotient-stage transitions. -/
@[stacks 09BB "successor compatibility of the quotient-domain comparison"]
theorem quotientComparison_step
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientComparison I M N n).comp
        (positiveStep I (ModuleCat.of R (M →ₗ[R] N)) n).hom =
      (quotientStep I M N n).comp (quotientComparison I M N (n + 1)) := sorry

/-- The component of the source-facing quotient-Hom comparison in the inverse-system category. -/
@[stacks 09BB "component of the quotient-domain comparison"]
noncomputable def quotientComparisonApp
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (positiveSystem I (ModuleCat.of R (M →ₗ[R] N))).obj (op n) ⟶
      (quotientSystem I M N).obj (op n) :=
  eqToHom (positiveSystem_obj I (ModuleCat.of R (M →ₗ[R] N)) n) ≫
    ModuleCat.ofHom (quotientComparison I M N n) ≫
      eqToHom (quotientSystem_obj I M N n).symm

/-- Consecutive source-facing comparison components satisfy the successor naturality square. -/
@[stacks 09BB "naturality of the quotient-domain comparison components"]
theorem quotientComparisonApp_naturality
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (positiveSystem I (ModuleCat.of R (M →ₗ[R] N))).stepMap n ≫
        quotientComparisonApp I M N n =
      quotientComparisonApp I M N (n + 1) ≫ (quotientSystem I M N).stepMap n := sorry

/-- The natural transformation from the positive quotient system of `Hom_R(M, N)` to the
source-facing quotient-domain Hom system. -/
@[stacks 09BB "natural quotient-domain Hom comparison"]
noncomputable def quotientComparisonNatTrans
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    positiveSystem I (ModuleCat.of R (M →ₗ[R] N)) ⟶ quotientSystem I M N :=
  NatTrans.ofOpSequence
    (fun n ↦ quotientComparisonApp I M N n)
    (quotientComparisonApp_naturality I M N)

/-- The `n`th component of the source-facing quotient-domain comparison. -/
@[simp, stacks 09BB "component formula for the quotient-domain comparison"]
theorem quotientComparisonNatTrans_app
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (quotientComparisonNatTrans I M N).app (op n) = quotientComparisonApp I M N n := sorry

/-- The comparison component between the canonical quotient system of `Hom_R(M, N)` and the
positive ideal-power Hom system. -/
@[stacks 09BB "component of the quotient Hom system comparison"]
noncomputable def comparisonApp
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (positiveSystem I (ModuleCat.of R (M →ₗ[R] N))).obj (op n) ⟶
      (system I M N).obj (op n) :=
  eqToHom (positiveSystem_obj I (ModuleCat.of R (M →ₗ[R] N)) n) ≫
    ModuleCat.ofHom (comparison I M N n) ≫
      eqToHom (system_obj I M N n).symm

/-- Consecutive comparison components satisfy the successor naturality square. -/
@[stacks 09BB "naturality of the quotient Hom system comparison"]
theorem comparisonApp_naturality
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (positiveSystem I (ModuleCat.of R (M →ₗ[R] N))).stepMap n ≫
        comparisonApp I M N n =
      comparisonApp I M N (n + 1) ≫ (system I M N).stepMap n := sorry

/-- The canonical natural transformation from the positive quotient system of `Hom_R(M, N)`
to the system `n ↦ Hom_R(M, N / I ^ (n + 1) N)`. -/
@[stacks 09BB "natural transformation comparing quotient of Hom with Hom of quotients"]
noncomputable def comparisonNatTrans
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N] :
    positiveSystem I (ModuleCat.of R (M →ₗ[R] N)) ⟶ system I M N :=
  NatTrans.ofOpSequence
    (fun n ↦ comparisonApp I M N n)
    (comparisonApp_naturality I M N)

/-- The `n`th component of the quotient-Hom system comparison is `comparisonApp`. -/
@[simp, stacks 09BB "component formula for the quotient Hom system comparison"]
theorem comparisonNatTrans_app
    (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (n : ℕ) :
    (comparisonNatTrans I M N).app (op n) = comparisonApp I M N n := sorry

end Ideal.PowerQuotient.Hom
