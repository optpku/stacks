/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor
public import ReasLib.Algebra.Module.CharacterModule.Evaluation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Evaluation as a natural transformation

For an arbitrary ring, character duality changes the scalar ring from `R`
to `Rᵐᵒᵖ`.  Applying it twice and restricting scalars along
`RingEquiv.opOp R` gives the canonical double-dual endofunctor on left
`R`-modules.  The commutative-ring presentation is retained as a simpler
specialization.

@stack 01DB
-/

open CategoryTheory

universe u v

noncomputable section

namespace CharacterModule

section Opposite

variable (R : Type u) [Ring R]

/-- The double character module of a left module over an arbitrary ring,
transported from `Rᵐᵒᵖᵐᵒᵖ` back to `R`. -/
@[stacks 01DB "double character module over a ring"]
abbrev opBidualObj (M : ModuleCat.{v} R) : ModuleCat.{v} R :=
  ModuleCat.of R (CharacterModule (CharacterModule M))

/-- Double character dualization as an endofunctor on left modules over an
arbitrary ring. -/
@[stacks 01DB "double character-module functor over a ring"]
abbrev opBidualFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  (opFunctor R).rightOp ⋙ opFunctor Rᵐᵒᵖ ⋙
    ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom

/-- The functorial double dual has the explicit double-character module as
its object value. -/
@[simp, stacks 01DB "double character functor object formula"]
theorem opBidualFunctor_obj (M : ModuleCat.{v} R) :
    (opBidualFunctor R).obj M = opBidualObj R M := sorry
/- Proof strategy: unfold `opBidualFunctor` and `opBidualObj`; the two
objects are definitionally equal. -/

/-- Evaluation is linear for the `R`-action obtained from the canonical
identification `R ≃+* Rᵐᵒᵖᵐᵒᵖ`. -/
@[stacks 01DB "linearity of arbitrary-ring character evaluation"]
theorem opEvaluation_map_smul (M : ModuleCat.{v} R) (r : R) (m : M) :
    (CharacterModule.eval (r • m) : (opBidualFunctor R).obj M) =
      r • (CharacterModule.eval m : (opBidualFunctor R).obj M) := sorry
/- Proof strategy: extensionality at `χ : CharacterModule M`, then use
`op_smul_apply` twice and the definition of restriction of scalars. -/

/-- Evaluation as an explicit `R`-linear map into the double character
module. -/
@[stacks 01DB "linear double-character evaluation over a ring"]
def opEvaluationLinear (M : ModuleCat.{v} R) :
    M →ₗ[R] opBidualObj R M :=
  { CharacterModule.eval with
    map_smul' := opEvaluation_map_smul R M }

/-- The underlying additive map of bundled evaluation. -/
@[stacks 01DB "additive character evaluation map"]
def opEvaluationAdd (M : ModuleCat.{v} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj ((opBidualFunctor R).obj M) :=
  AddCommGrpCat.ofHom (opEvaluationLinear R M).toAddMonoidHom

/-- The underlying additive map commutes with the scalar actions. -/
@[stacks 01DB "scalar naturality of character evaluation"]
theorem opEvaluation_smul_naturality (M : ModuleCat.{v} R) (r : R) :
    opEvaluationAdd R M ≫ ((opBidualFunctor R).obj M).smul r =
      M.smul r ≫ opEvaluationAdd R M := sorry

/-- The bundled evaluation morphism into the double character module. -/
@[stacks 01DB "bundled arbitrary-ring character evaluation"]
def opEvaluationApp (M : ModuleCat.{v} R) :
    M ⟶ (opBidualFunctor R).obj M :=
  ModuleCat.homMk (opEvaluationAdd R M) (opEvaluation_smul_naturality R M)

/-- Arbitrary-ring evaluation has the expected pointwise formula. -/
@[simp, stacks 01DB "pointwise arbitrary-ring character evaluation"]
theorem opEvaluationApp_apply (M : ModuleCat.{v} R) (m : M)
    : (opEvaluationAdd R M).hom m = CharacterModule.eval m := sorry
/- Proof strategy: unfold `opEvaluationApp` and `opEvaluationAdd`, then
apply `CharacterModule.eval_apply`. -/

/-- Evaluation into the arbitrary-ring double dual is natural. -/
@[stacks 01DB "naturality of arbitrary-ring character evaluation"]
theorem opEvaluation_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f ≫ opEvaluationApp R N =
      opEvaluationApp R M ≫ (opBidualFunctor R).map f := sorry
/- Proof strategy: extensionality on a module element and a character, then
use `opEvaluationApp_apply` and the pointwise formula for `opFunctor`. -/

/-- The canonical natural transformation from a left module over an
arbitrary ring to its double character module. -/
@[stacks 01DB "natural evaluation into the double character module over a ring"]
def opEvaluation : 𝟭 (ModuleCat.{v} R) ⟶ opBidualFunctor R where
  app := opEvaluationApp R
  naturality := fun {_ _} f ↦ opEvaluation_naturality R f

/-- Every arbitrary-ring double-dual evaluation component is injective on
elements. -/
@[stacks 01DB "injectivity of bundled character evaluation over a ring"]
theorem opEvaluationApp_injective (M : ModuleCat.{v} R) :
    Function.Injective (opEvaluationApp R M) := sorry
/- Proof strategy: forget the scalar actions and apply
`CharacterModule.eval_injective`. -/

/-- Every arbitrary-ring double-dual evaluation component is a
monomorphism. -/
@[stacks 01DB "monomorphism of arbitrary-ring character evaluation"]
instance mono_opEvaluationApp (M : ModuleCat.{v} R) :
    Mono (opEvaluationApp R M) := sorry
/- Proof strategy: combine `ModuleCat.mono_iff_injective` with
`opEvaluationApp_injective`. -/

end Opposite

section Commutative

variable (R : Type u) [CommRing R]

/-- The double character-module endofunctor. -/
@[stacks 01DB "commutative double character functor"]
abbrev bidualFunctor : ModuleCat.{v} R ⥤ ModuleCat.{v} R :=
  (functor R).rightOp ⋙ functor R

/-- Evaluation at one module, bundled as a morphism to its double character
module. -/
@[stacks 01DB "commutative character evaluation component"]
def evaluationApp (M : ModuleCat.{v} R) :
    M ⟶ (bidualFunctor R).obj M :=
  ModuleCat.ofHom (evalLinear R)

/-- Evaluation is natural with respect to module maps. -/
@[stacks 01DB "naturality of commutative character evaluation"]
theorem evaluation_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    f ≫ evaluationApp R N =
      evaluationApp R M ≫ (bidualFunctor R).map f := sorry
/- Proof strategy: extensionality on a module element and a character, then
use the pointwise formulas for `dualMap` and `evalLinear`. -/

/-- The canonical natural transformation from a module to its double
character module. -/
@[stacks 01DB "natural evaluation into the double character module"]
def evaluation : 𝟭 (ModuleCat.{v} R) ⟶ bidualFunctor R where
  app := evaluationApp R
  naturality := fun {_ _} f ↦ evaluation_naturality R f

/-- The underlying linear map of natural evaluation is the canonical linear
evaluation map. -/
@[simp, stacks 01DB "underlying commutative evaluation map"]
theorem evaluation_app_hom (M : ModuleCat.{v} R) :
    ((evaluation R).app M).hom = evalLinear R := sorry
/- Proof strategy: unfold `evaluation` and `evaluationApp`. -/

/-- Every component of character evaluation is injective. -/
@[stacks 01DB "injectivity of commutative character evaluation"]
theorem evaluation_app_injective (M : ModuleCat.{v} R) :
    Function.Injective ((evaluation R).app M) := sorry
/- Proof strategy: identify the underlying map with `evalLinear R` and apply
`evalLinear_injective`. -/

/-- Every component of character evaluation is a monomorphism. -/
@[stacks 01DB "monomorphism of commutative character evaluation"]
instance mono_evaluationApp (M : ModuleCat.{v} R) :
    Mono ((evaluation R).app M) := sorry
/- Proof strategy: use `ModuleCat.mono_iff_injective` and
`evaluation_app_injective`. -/

end Commutative

end CharacterModule
