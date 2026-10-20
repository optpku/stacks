/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Linear.Yoneda
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor

@[expose] public section

/-!
# Tensor–Hom duality for character modules

Character duality carries a tensor product to the module of linear maps into a
character module, naturally in both module variables.
-/

open CategoryTheory
open scoped MonoidalCategory

universe u

namespace CharacterModule.TensorHom

variable (R : Type u) [CommRing R]

/-- The contravariant bifunctor sending `(M₁, M₂)` to the character module of
`M₁ ⊗[R] M₂`. -/
@[reducible]
def tensorFunctor :
    (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (MonoidalCategory.tensor (ModuleCat.{u} R)).op ⋙ CharacterModule.functor R

/-- The contravariant bifunctor sending `(M₁, M₂)` to
`ModuleCat.of R (M₁ ⟶ CharacterModule.moduleObj R M₂)`. -/
@[reducible]
def homFunctor :
    (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (prodOpEquiv (ModuleCat.{u} R)).functor ⋙
    (𝟭 (ModuleCat.{u} R)ᵒᵖ).prod (CharacterModule.functor R) ⋙
      Functor.uncurry.obj (linearCoyoneda R (ModuleCat.{u} R))

/-- The tensor endpoint at `X` is the character module of the tensor product. -/
theorem tensorFunctor_obj
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ) :
    (tensorFunctor R).obj X =
      CharacterModule.moduleObj R (X.unop.1 ⊗ X.unop.2) := sorry

/-- The Hom endpoint at `X` is the module of linear maps into the character module. -/
theorem homFunctor_obj
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ) :
    (homFunctor R).obj X =
      ModuleCat.of R (X.unop.1 ⟶ CharacterModule.moduleObj R X.unop.2) := sorry

/-- Character currying as a linear equivalence at `X`. -/
noncomputable def appEquiv
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ) :
    CharacterModule (TensorProduct R X.unop.1 X.unop.2) ≃ₗ[R]
      (X.unop.1 ⟶ CharacterModule.moduleObj R X.unop.2) :=
  (CharacterModule.homEquiv
    (R := R) (A := X.unop.1) (B := X.unop.2)).symm.trans
    (ModuleCat.homLinearEquiv :
      (X.unop.1 ⟶ CharacterModule.moduleObj R X.unop.2) ≃ₗ[R]
        (X.unop.1 →ₗ[R] CharacterModule X.unop.2)).symm

/-- Character currying as an isomorphism between the two functor values at `X`. -/
noncomputable def appIso
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ) :
    (tensorFunctor R).obj X ≅ (homFunctor R).obj X :=
  (appEquiv R X).toModuleIso

/-- The forward component sends `χ` to `m₁ ↦ m₂ ↦ χ (m₁ ⊗ₜ[R] m₂)`. -/
theorem appEquiv_apply
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ)
    (χ : CharacterModule (TensorProduct R X.unop.1 X.unop.2))
    (m₁ : X.unop.1) (m₂ : X.unop.2) :
    appEquiv R X χ m₁ m₂ = χ (m₁ ⊗ₜ[R] m₂) := sorry

/-- The inverse component evaluates a linear map on pure tensors. -/
theorem appEquiv_symm_tmul
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ)
    (g : X.unop.1 ⟶ CharacterModule.moduleObj R X.unop.2)
    (m₁ : X.unop.1) (m₂ : X.unop.2) :
    (appEquiv R X).symm g (m₁ ⊗ₜ[R] m₂) = g m₁ m₂ := sorry

/-- The pointwise character currying isomorphisms are natural in both module variables. -/
theorem appIso_hom_naturality
    {X Y : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ} (f : X ⟶ Y) :
    (tensorFunctor R).map f ≫ (appIso R Y).hom =
      (appIso R X).hom ≫ (homFunctor R).map f := sorry

/-- The natural character currying isomorphism in both module variables. -/
noncomputable def iso : tensorFunctor R ≅ homFunctor R :=
  NatIso.ofComponents (appIso R) (appIso_hom_naturality R)

/-- The component of the natural isomorphism is the pointwise character currying map. -/
theorem iso_hom_app
    (X : (ModuleCat.{u} R × ModuleCat.{u} R)ᵒᵖ) :
    (iso R).hom.app X = (appIso R X).hom := sorry

end CharacterModule.TensorHom
