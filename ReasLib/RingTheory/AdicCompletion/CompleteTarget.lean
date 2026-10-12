/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps from adic completions to complete module targets

@stack 0BNG

This leaf records the module-level comparison map from an adic completion to
an already complete target.  It is independent of local-ring, finiteness, and
presentation hypotheses.  The nilpotent-target completeness criterion is kept
separate from the map so applications can supply any available completeness
instance.
-/

noncomputable section

universe u v w x

namespace IsAdicComplete

variable {R : Type u} [CommRing R]
variable {Q : Type v} [AddCommGroup Q] [Module R Q]

/-- Tag `0BNG`: a module killed by a power of the defining ideal is adically complete. -/
@[stacks 0BNG "power-annihilated target is adically complete"]
theorem of_pow_smul_top_eq_bot (I : Ideal R) (c : ℕ)
    (h : I ^ c • (⊤ : Submodule R Q) = ⊥) : IsAdicComplete I Q := sorry

end IsAdicComplete

namespace AdicCompletion

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} {Q : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup Q] [Module R Q]

/-- Tag `0BNG`: the map from the `I`-adic completion of `N` to an `I`-adically complete target
induced by `g : N →ₗ[R] Q`. -/
@[stacks 0BNG "adic completion to a complete target"]
noncomputable def mapToComplete (I : Ideal R) (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    AdicCompletion I N →ₗ[R] Q :=
  ((ofLinearEquiv I Q).symm : AdicCompletion I Q →ₗ[R] Q).comp
    ((map I g).restrictScalars R)

/-- The canonical map from an adic completion to a target annihilated by a power of the
defining ideal.  The completeness witness is supplied explicitly, so consumers do not need to
install a local `IsAdicComplete` instance. -/
@[stacks 0BNG "completion map to a power-annihilated target"]
noncomputable def mapToPowSmulTopEqBot (I : Ideal R) (g : N →ₗ[R] Q) {c : ℕ}
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) : AdicCompletion I N →ₗ[R] Q :=
  @mapToComplete R _ N Q _ _ _ _ I g
    (IsAdicComplete.of_pow_smul_top_eq_bot I c hc)

/-- Tag `0BNG`: `mapToComplete` extends its defining map on the canonical dense image. -/
@[simp, stacks 0BNG "adic completion to a complete target"]
theorem mapToComplete_of (I : Ideal R) (g : N →ₗ[R] Q) [IsAdicComplete I Q] (x : N) :
    mapToComplete I g (of I N x) = g x := sorry

/-- The map to a power-annihilated target extends the original map on the canonical image. -/
@[simp, stacks 0BNG "completion map to a power-annihilated target"]
theorem mapToPowSmulTopEqBot_of (I : Ideal R) (g : N →ₗ[R] Q) {c : ℕ}
    (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) (x : N) :
    mapToPowSmulTopEqBot I g hc (of I N x) = g x := sorry

/-- Tag `0BNG`: composing `mapToComplete` with the canonical map into the completion recovers
the original map. -/
@[simp, stacks 0BNG "adic completion to a complete target"]
theorem mapToComplete_comp_of (I : Ideal R) (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    (mapToComplete I g).comp (of I N) = g := sorry

/-- Tag `0BNG`: extension to a complete target commutes with completion functoriality. -/
@[simp, stacks 0BNG "adic completion to a complete target"]
theorem mapToComplete_comp_map
    (I : Ideal R) (f : M →ₗ[R] N) (g : N →ₗ[R] Q) [IsAdicComplete I Q] :
    (mapToComplete I g).comp ((map I f).restrictScalars R) =
      mapToComplete I (g.comp f) := sorry

/-- Tag `0BNG`: an extended map to a complete target vanishes after a completed map whenever
the original composite vanishes. -/
@[stacks 0BNG "adic completion to a complete target"]
theorem mapToComplete_comp_eq_zero
    (I : Ideal R) {f : M →ₗ[R] N} {g : N →ₗ[R] Q} [IsAdicComplete I Q]
    (h : g.comp f = 0) :
    (mapToComplete I g).comp ((map I f).restrictScalars R) = 0 := sorry

/-- Tag `0BNG`: extending a surjective map to an adically complete target remains surjective. -/
@[stacks 0BNG "adic completion to a complete target"]
theorem mapToComplete_surjective
    (I : Ideal R) {g : N →ₗ[R] Q} [IsAdicComplete I Q]
    (hg : Function.Surjective g) :
    Function.Surjective (mapToComplete I g) := sorry

end AdicCompletion
