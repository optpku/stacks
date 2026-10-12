/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.RingTheory.AdicCompletion.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complete modules over an adic completion

An `I`-adically complete `R`-module carries a canonical action of the completed
ring `AdicCompletion I R`.  This file owns that concrete action, its comparison
with the ordinary module completion, and the finite-generation bridge used for
derived-complete modules over Noetherian rings.

@stack 09BA
-/

@[expose] public section

noncomputable section

universe u v

namespace IsAdicComplete

variable {R : Type u} [CommRing R]
variable {I : Ideal R} {M : Type v} [AddCommGroup M] [Module R M]

/-- The canonical `AdicCompletion I R`-module structure on an already
`I`-adically complete `R`-module, transported from `AdicCompletion I M` along
`AdicCompletion.ofLinearEquiv I M`. -/
@[implicit_reducible, stacks 09BA "canonical completed-module action"]
noncomputable def completedModule [IsAdicComplete I M] :
    Module (AdicCompletion I R) M :=
  Module.compHom M <|
    ((AdicCompletion.ofLinearEquiv I M).symm.conjRingEquiv.toRingHom).comp
      (Module.toModuleEnd R (AdicCompletion I M))

-- Local instance justification (instance diamond): use the transported action
-- only while building its API; exporting it globally would compete with
-- `AdicCompletion.module` when `M` is itself an adic completion.
attribute [local instance] completedModule

/-- The ordinary completion equivalence respects the canonical action of the
completed coefficient ring. -/
@[stacks 09BA "completed-module scalar compatibility"]
theorem completionLinearEquiv_map_smul [IsAdicComplete I M]
    (a : AdicCompletion I R) (x : M) :
    AdicCompletion.ofLinearEquiv I M (a • x) =
      a • AdicCompletion.ofLinearEquiv I M x := sorry

/-- The canonical equivalence from a complete module to its ordinary adic
completion, linear over the completed coefficient ring. -/
@[stacks 09BA "completed-module linear equivalence"]
noncomputable def completionLinearEquiv [IsAdicComplete I M] :
    M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  { toFun := AdicCompletion.ofLinearEquiv I M
    invFun := (AdicCompletion.ofLinearEquiv I M).symm
    left_inv := (AdicCompletion.ofLinearEquiv I M).left_inv
    right_inv := (AdicCompletion.ofLinearEquiv I M).right_inv
    map_add' := (AdicCompletion.ofLinearEquiv I M).map_add
    map_smul' := completionLinearEquiv_map_smul }

/-- A complete module over a Noetherian ring is finite over the completed
coefficient ring when its reduction modulo the defining ideal is finite. -/
@[stacks 09BA "complete-module finite-generation bridge"]
theorem moduleFinite_of_finite_quotient
    [IsNoetherianRing R] [IsAdicComplete I M]
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Finite (AdicCompletion I R) M := sorry

end IsAdicComplete
