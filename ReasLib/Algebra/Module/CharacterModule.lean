/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Character modules over opposite rings

An additive character on a left `R`-module is canonically a left
`Rᵐᵒᵖ`-module. This leaf exposes that scalar action and the corresponding
contravariant linear map without imposing commutativity on `R`.
-/

universe u v w

namespace CharacterModule

variable {R : Type u} [Semiring R]

/-- The canonical left `Rᵐᵒᵖ`-module structure on additive characters of a
left `R`-module. -/
@[stacks 01D9 "opposite scalar action on character modules"]
instance instModuleOpposite (M : Type v) [AddCommGroup M] [Module R M] :
    Module Rᵐᵒᵖ (CharacterModule M) :=
  AddMonoidHom.instDomMulActModule

section OppositeDual

variable (R : Type u) [Semiring R]

/-- The canonical `R`-module structure on the character dual of an
`Rᵐᵒᵖ`-module, obtained by restricting along `RingEquiv.opOp R`. -/
@[stacks 01DB "opposite-ring scalar action on second character duals"]
instance (priority := 900) opDualModule (M : Type v) [AddCommGroup M]
    [Module Rᵐᵒᵖ M] : Module R (CharacterModule M) :=
  Module.compHom _ (RingEquiv.opOp R).toRingHom

end OppositeDual

/-- Opposite scalars act on a character by precomposition with the original
scalar action. -/
@[simp]
theorem op_smul_apply {M : Type v} [AddCommGroup M] [Module R M]
    (r : Rᵐᵒᵖ) (χ : CharacterModule M) (m : M) :
    (r • χ) m = χ (MulOpposite.unop r • m) := sorry
/- Proof strategy: use `DomMulAct.smul_addMonoidHom_apply`. -/

/-- Precomposition with an `R`-linear map respects the opposite scalar
action on character modules. -/
theorem dual_map_op_smul {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (r : Rᵐᵒᵖ) (χ : CharacterModule N) :
    CharacterModule.dual f.toAddMonoidHom.toIntLinearMap (r • χ) =
      r • CharacterModule.dual f.toAddMonoidHom.toIntLinearMap χ := sorry
/- Proof strategy: extensionality at `m : M`, then use `op_smul_apply` and
`f.map_smul`. -/

/-- The character dual of an `R`-linear map, linear over `Rᵐᵒᵖ`. -/
def dualOpposite {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    CharacterModule N →ₗ[Rᵐᵒᵖ] CharacterModule M :=
  { CharacterModule.dual f.toAddMonoidHom.toIntLinearMap with
    map_smul' := dual_map_op_smul f }

/-- Opposite-linear character dualization is precomposition on elements. -/
@[simp]
theorem dualOpposite_apply {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (χ : CharacterModule N) (m : M) :
    dualOpposite f χ m = χ (f m) := sorry
/- Proof strategy: unfold `dualOpposite` and use
`CharacterModule.dual_apply`. -/

/-- Character dualization sends identity maps to identity maps. -/
@[simp]
theorem dualOpposite_id (M : Type v) [AddCommGroup M] [Module R M] :
    dualOpposite (LinearMap.id : M →ₗ[R] M) = LinearMap.id := sorry
/- Proof strategy: extensionality on a character and a module element, then
use `dualOpposite_apply`. -/

/-- Character dualization reverses composition. -/
theorem dualOpposite_comp {M : Type v} {N : Type w} {P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    dualOpposite (g.comp f) = (dualOpposite f).comp (dualOpposite g) := sorry
/- Proof strategy: extensionality on a character and a module element, then
use `dualOpposite_apply`. -/

/-- Character dualization preserves addition of linear maps. -/
theorem dualOpposite_add {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f g : M →ₗ[R] N) :
    dualOpposite (f + g) = dualOpposite f + dualOpposite g := sorry
/- Proof strategy: extensionality on a character and a module element, then
use `dualOpposite_apply` and additivity of the character. -/

/-- Character dualization sends the zero map to the zero map. -/
@[simp]
theorem dualOpposite_zero {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    dualOpposite (0 : M →ₗ[R] N) = 0 := sorry
/- Proof strategy: extensionality and `dualOpposite_apply`, followed by
`map_zero`. -/

end CharacterModule
