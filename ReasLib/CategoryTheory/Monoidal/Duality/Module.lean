/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Exact pairings of modules

An exact pairing of modules over a commutative ring makes both modules finite projective and
identifies either chosen dual with the corresponding linear dual.  Over a field, the associated
bilinear form is finite-dimensional and nondegenerate.  The API takes the exact pairing explicitly,
so consumers do not need to alter the local instance environment.

@stack 0FNJ
-/

@[expose] public section

universe u

namespace CategoryTheory.ExactPairing

open CategoryTheory.MonoidalCategory
open scoped TensorProduct

section CommRing

variable {R : Type u} [CommRing R]
variable {M N : ModuleCat R}

/-- The closed-monoidal dual of a module is its ordinary linear dual. -/
@[stacks 0FNJ "closed-monoidal dual of a module"]
noncomputable def closedDualIso (M : ModuleCat R) :
    MonoidalClosed.dual M ≅ ModuleCat.of R (Module.Dual R M) :=
  (ModuleCat.homLinearEquiv :
    (M ⟶ 𝟙_ (ModuleCat R)) ≃ₗ[R] Module.Dual R M).toModuleIso

/-- Applying a functional to the first tensor factor of a raw coevaluation element. -/
@[stacks 0FNJ "module dual comparison on elements"]
def fromCoevaluationFn (η : 𝟙_ (ModuleCat R) ⟶ M ⊗ N) (φ : Module.Dual R M) : N :=
  (TensorProduct.lid R N)
    ((TensorProduct.map φ (LinearMap.id : N →ₗ[R] N))
      (η (1 : R)))

/-- The raw coevaluation formula is additive in the functional. -/
@[stacks 0FNJ "additivity of the coevaluation comparison"]
theorem fromCoevaluationFn_add
    (η : 𝟙_ (ModuleCat R) ⟶ M ⊗ N) (φ ψ : Module.Dual R M) :
    fromCoevaluationFn η (φ + ψ) = fromCoevaluationFn η φ + fromCoevaluationFn η ψ := sorry

/-- The raw coevaluation formula commutes with scalar multiplication. -/
@[stacks 0FNJ "scalar compatibility of the coevaluation comparison"]
theorem fromCoevaluationFn_smul
    (η : 𝟙_ (ModuleCat R) ⟶ M ⊗ N) (r : R) (φ : Module.Dual R M) :
    fromCoevaluationFn η (r • φ) = r • fromCoevaluationFn η φ := sorry

/-- A raw coevaluation determines a linear map from `Module.Dual R M` to `N`. -/
@[stacks 0FNJ "linear map induced by coevaluation"]
def fromCoevaluationLinear (η : 𝟙_ (ModuleCat R) ⟶ M ⊗ N) :
    Module.Dual R M →ₗ[R] N where
  toFun := fromCoevaluationFn η
  map_add' := fromCoevaluationFn_add η
  map_smul' := fromCoevaluationFn_smul η

/-- A raw coevaluation determines a morphism from `Module.Dual R M` to `N`. -/
@[stacks 0FNJ "module morphism induced by coevaluation"]
def fromCoevaluation (η : 𝟙_ (ModuleCat R) ⟶ M ⊗ N) :
    ModuleCat.of R (Module.Dual R M) ⟶ N :=
  ModuleCat.ofHom (fromCoevaluationLinear η)

/-- Applying a functional to the first tensor factor of an exact-pairing coevaluation. -/
@[stacks 0FNJ "module dual comparison on elements"]
def fromModuleDualFn (p : ExactPairing M N) (phi : Module.Dual R M) : N :=
  fromCoevaluationFn p.coevaluation' phi

/-- The coevaluation formula as a linear map from the linear dual of `M` to `N`. -/
@[stacks 0FNJ "module dual comparison"]
def fromModuleDualLinear (p : ExactPairing M N) : Module.Dual R M →ₗ[R] N where
  toFun := p.fromModuleDualFn
  map_add' := fromCoevaluationFn_add p.coevaluation'
  map_smul' := fromCoevaluationFn_smul p.coevaluation'

/-- The canonical map from the linear dual of `M` to its chosen left dual `N`. -/
@[stacks 0FNJ "module dual comparison"]
def fromModuleDual (p : ExactPairing M N) :
    ModuleCat.of R (Module.Dual R M) ⟶ N :=
  fromCoevaluation p.coevaluation'

/-- A raw evaluation determines a morphism from `N` to `Module.Dual R M`. -/
@[stacks 0FNJ "module morphism induced by evaluation"]
noncomputable def toModuleDualOfEvaluation (ε : N ⊗ M ⟶ 𝟙_ (ModuleCat R)) :
    N ⟶ ModuleCat.of R (Module.Dual R M) :=
  MonoidalClosed.curry ((β_ M N).hom ≫ ε) ≫ (closedDualIso M).hom

/-- The inverse comparison from a chosen left dual `N` to the linear dual of `M`. -/
@[stacks 0FNJ "inverse module dual comparison"]
noncomputable def toModuleDual (p : ExactPairing M N) :
    N ⟶ ModuleCat.of R (Module.Dual R M) :=
  toModuleDualOfEvaluation p.evaluation'

/-- The canonical source-order identification `Module.Dual R M ≅ N` associated to
`p : ExactPairing M N`.  Its maps are the explicit coevaluation and evaluation formulas; only
their inverse laws use the triangle identities. -/
@[stacks 0FNJ "module dual identification"]
noncomputable def moduleDualIso (p : ExactPairing M N) :
    ModuleCat.of R (Module.Dual R M) ≅ N where
  hom := p.fromModuleDual
  inv := p.toModuleDual
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The first member of an exact pairing of modules is finite projective. -/
@[stacks 0FNJ "left duals are finite projective"]
theorem left_finiteProjective (p : ExactPairing M N) :
    Module.FiniteProjective R M := sorry

/-- The second member of an exact pairing of modules is finite projective. -/
@[stacks 0FNJ "right duals are finite projective"]
theorem right_finiteProjective (p : ExactPairing M N) :
    Module.FiniteProjective R N := sorry

/-- The canonical map `Module.Dual R M ⟶ N` applies a functional to the first tensor factor
of the coevaluation element. -/
@[stacks 0FNJ "module dual comparison on elements"]
theorem fromModuleDual_apply (p : ExactPairing M N) (φ : Module.Dual R M) :
    p.fromModuleDual φ = p.fromModuleDualFn φ := sorry

/-- Evaluating the inverse module-dual comparison recovers the original exact-pairing
evaluation `ε(n,m)`. -/
@[stacks 0FNJ "module dual comparison on elements"]
theorem toModuleDual_apply (p : ExactPairing M N) (n : N) (m : M) :
    p.evaluation' (n ⊗ₜ[R] m) = p.toModuleDual n m := sorry

end CommRing

variable {F : Type u} [Field F]
variable {M N : ModuleCat F}

/-- The curried linear evaluation associated to an explicit exact pairing of modules. -/
@[stacks 0FNJ "curried evaluation over a field"]
def evaluationLinear (p : ExactPairing M N) : N →ₗ[F] M →ₗ[F] F :=
  TensorProduct.curry p.evaluation'.hom

/-- Evaluation of the curried pairing on a pair of vectors agrees with evaluation on their pure
tensor. -/
@[stacks 0FNJ "pure-tensor evaluation formula over a field"]
theorem evaluationLinear_apply (p : ExactPairing M N) (n : N) (m : M) :
    p.evaluationLinear n m = p.evaluation'.hom (n ⊗ₜ[F] m) := sorry

/-- The first member of an exact pairing of vector spaces is finite dimensional. -/
@[stacks 0FNJ "left finite-dimensional field specialization"]
theorem left_finiteDimensional (p : ExactPairing M N) : FiniteDimensional F M := sorry

/-- The second member of an exact pairing of vector spaces is finite dimensional. -/
@[stacks 0FNJ "right finite-dimensional field specialization"]
theorem right_finiteDimensional (p : ExactPairing M N) : FiniteDimensional F N := sorry

/-- The evaluation of an exact pairing of vector spaces is nondegenerate. -/
@[stacks 0FNJ "nondegenerate field evaluation"]
theorem evaluationLinear_nondegenerate (p : ExactPairing M N) :
    p.evaluationLinear.Nondegenerate := sorry

end CategoryTheory.ExactPairing
