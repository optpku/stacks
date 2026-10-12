/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Finite Free Module Models

Mathlib presents free modules through finitely supported functions, while many
finite-presentation arguments naturally use ordinary functions on a finite
basis.  This leaf packages the existing linear equivalences as isomorphisms in
`ModuleCat`, together with reindexing by an equivalence of basis types.

The linear equivalence itself remains owned by
`Finsupp.linearEquivFunOnFinite`; this file only supplies the categorical
surface needed by constructions expressed in `ModuleCat`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

section FiniteFree

variable {R : Type u} [Ring R]
variable {I J : Type v}

/-- A finite free module in the finitely supported-function model is canonically isomorphic in
`ModuleCat` to the same module in the ordinary function model. -/
noncomputable def finsuppToFunIso [Finite I] :
    ModuleCat.of R (I →₀ R) ≅ ModuleCat.of R (I → R) :=
  (Finsupp.linearEquivFunOnFinite R R I).toModuleIso

/-- A finite free module in the ordinary function model is canonically isomorphic in `ModuleCat`
to the same module in the finitely supported-function model. -/
noncomputable def funToFinsuppIso [Finite I] :
    ModuleCat.of R (I → R) ≅ ModuleCat.of R (I →₀ R) :=
  (finsuppToFunIso (R := R) (I := I)).symm

/-- The forward map of `finsuppToFunIso` evaluates a finitely supported function pointwise. -/
@[simp]
theorem finsuppToFunIso_hom_apply [Finite I] (f : I →₀ R) (i : I) :
    (finsuppToFunIso (R := R) (I := I)).hom f i = f i := sorry

/-- The forward map of `funToFinsuppIso` is the inverse of the canonical finite-support
evaluation equivalence. -/
@[simp]
theorem funToFinsuppIso_hom_apply [Finite I] (f : I → R) :
    (funToFinsuppIso (R := R) (I := I)).hom f =
      (Finsupp.linearEquivFunOnFinite R R I).symm f := sorry

/-- Reindexing the function-model free module along a basis equivalence.  The orientation of
`e : J ≃ I` sends an `I`-indexed function to the `J`-indexed function `j ↦ f (e j)`. -/
noncomputable def functionReindexIso (e : J ≃ I) :
    ModuleCat.of R (I → R) ≅ ModuleCat.of R (J → R) :=
  (LinearEquiv.funCongrLeft R R e).toModuleIso

/-- `functionReindexIso` evaluates a reindexed function at `j` by evaluating the original
function at `e j`. -/
@[simp]
theorem functionReindexIso_hom_apply (e : J ≃ I) (f : I → R) (j : J) :
    (functionReindexIso (R := R) e).hom f j = f (e j) := sorry

/-- Reindex an ordinary-function free module and then pass to the finitely supported model on
the target finite basis.  This is useful when a construction fixes the source basis convention
but its target is expressed using `Finsupp`. -/
noncomputable def functionToFinsuppIsoOfEquiv [Finite J] (e : J ≃ I) :
    ModuleCat.of R (I → R) ≅ ModuleCat.of R (J →₀ R) :=
  functionReindexIso (R := R) e ≪≫ funToFinsuppIso (R := R) (I := J)

/-- The composite `functionToFinsuppIsoOfEquiv` has the expected finitely supported coordinate
description. -/
@[simp]
theorem functionToFinsuppIsoOfEquiv_hom_apply [Finite J] (e : J ≃ I) (f : I → R) :
    (functionToFinsuppIsoOfEquiv (R := R) e).hom f =
      (Finsupp.linearEquivFunOnFinite R R J).symm (fun j ↦ f (e j)) := sorry

/-- The standard finite free module on `Fin n` is unchanged when its function-model basis is
lifted to the universe of the coefficient ring. -/
noncomputable def finFunctionToUliftFunctionIso (n : ℕ) :
    ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (ULift.{u} (Fin n) → R) :=
  (LinearEquiv.funCongrLeft R R
    (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toModuleIso

/-- The lifted-basis function is evaluated by lowering its `ULift` index. -/
@[simp]
theorem finFunctionToUliftFunctionIso_hom_apply (n : ℕ) (f : Fin n → R)
    (i : ULift.{u} (Fin n)) :
    (finFunctionToUliftFunctionIso (R := R) n).hom f i = f i.down := sorry

/-- The standard finite free module on `Fin n` identifies with the finitely supported free
module indexed by `ULift (Fin n)`. -/
noncomputable def finFunctionToUliftFinsuppIso (n : ℕ) :
    ModuleCat.of R (Fin n → R) ≅ ModuleCat.of R (ULift.{u} (Fin n) →₀ R) :=
  finFunctionToUliftFunctionIso (R := R) n ≪≫
    funToFinsuppIso (R := R) (I := ULift.{u} (Fin n))

/-- The finitely supported model of a lifted finite-basis function has the original coordinate
at each lifted index. -/
@[simp]
theorem finFunctionToUliftFinsuppIso_hom_apply (n : ℕ) (f : Fin n → R)
    (i : ULift.{u} (Fin n)) :
    ((finFunctionToUliftFinsuppIso (R := R) n).hom f) i = f i.down := sorry

end FiniteFree

end ModuleCat
