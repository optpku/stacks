/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The finite underlying set sheaf of a finite module local system

The supplied module charts are mapped through the actual forgetful sheaf functor.
Native commutation of constant sheaves with that functor gives the underlying set
charts, whose carriers are finite because the coefficient ring and modules are finite.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type (max u v)} [Ring Λ] [Finite Λ]
variable [HasWeakSheafify J (ModuleCat.{max u v} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v} Λ)]

/-- Forgetting a finite-type local system over finite coefficients retains its actual
constant charts and makes their underlying finite sets the local models. -/
instance underlying_isFiniteLocallyConstant (F : Sheaf J (ModuleCat.{max u v} Λ))
    [IsFiniteTypeLocallyConstantModule F] :
    IsFiniteLocallyConstant ((sheafCompose J (forget (ModuleCat.{max u v} Λ))).obj F) where
  existsConstantCover U := by
    obtain ⟨I, charts, hcover, models⟩ :=
      IsLocallyConstantWith.existsConstantCover
        (P := fun M : ModuleCat.{max u v} Λ ↦ Module.Finite Λ M) (F := F) U
    refine ⟨I, charts, hcover, ?_⟩
    intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := models i
    letI : Module.Finite Λ M := hM
    refine ⟨M, Module.finite_of_finite Λ (M := M), ?_⟩
    exact ⟨((sheafCompose (J.over (charts i).left) (forget (ModuleCat.{max u v} Λ))).mapIso e) ≪≫
      (constantCommuteCompose (J.over (charts i).left) (forget (ModuleCat.{max u v} Λ))).app M⟩

end CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule
