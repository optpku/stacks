/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricPower
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower.LeftTensor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Left tensor maps for symmetric-power presheaves

This file lifts the canonical `M ⊗ Sym^n(N) ⟶ Sym^(n + 1)(N)` morphism sectionwise to module
presheaves over an arbitrary commutative ring presheaf.  Naturality and the zero-composite API are
owned here rather than rebuilt in geometric applications.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricPower

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The sectionwise left-tensor morphism
`F ⊗ Sym^n(G) ⟶ Sym^(n + 1)(G)` induced by `f : F ⟶ G`. -/
@[stacks 01CG "sectionwise symmetric left tensor map"]
noncomputable def leftTensorHom
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) (n : ℕ) :
    PresheafOfModules.Monoidal.tensorObj F (presheaf 𝒪 G n) ⟶
      presheaf 𝒪 G (n + 1) where
  app U := ModuleCat.symmetricPower.leftTensorMap (homApp 𝒪 f U) n
  naturality := sorry

/-- The component of the sectionwise symmetric left-tensor morphism is the bundled
`ModuleCat` left-tensor map. -/
theorem leftTensorHom_app
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ) :
    (leftTensorHom 𝒪 f n).app U =
      ModuleCat.symmetricPower.leftTensorMap (homApp 𝒪 f U) n := sorry

/-- The sectionwise symmetric left-tensor morphism on a pure tensor of a pure symmetric
tensor. -/
@[simp]
theorem leftTensorHom_app_tmul_mk
    {F G : PresheafOfModules.{w} (RingPresheaf 𝒪)} (f : F ⟶ G) (n : ℕ) (U : Cᵒᵖ)
    (x : sectionObj 𝒪 F U) (m : SymmetricPower.UFin n → sectionObj 𝒪 G U) :
    (leftTensorHom 𝒪 f n).app U (x ⊗ₜ ModuleCat.symmetricPower.mk m) =
      ModuleCat.symmetricPower.mk
        (SymmetricPower.cons (homApp 𝒪 f U x) m) := sorry

/-- Naturality of the symmetric left-tensor construction in a commuting square of module
presheaves. -/
theorem leftTensorHom_naturality
    {F₁ F₂ G₁ G₂ : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂) (f₁ : F₁ ⟶ G₁) (f₂ : F₂ ⟶ G₂)
    (h : a ≫ f₂ = f₁ ≫ b) (n : ℕ) :
    PresheafOfModules.Monoidal.tensorHom a (hom 𝒪 b n) ≫ leftTensorHom 𝒪 f₂ n =
      leftTensorHom 𝒪 f₁ n ≫ hom 𝒪 b (n + 1) := sorry

/-- A symmetric-power presheaf map annihilates the preceding left-tensor map whenever the
underlying module-presheaf composite vanishes. -/
theorem leftTensorHom_comp_eq_zero
    {F G H : PresheafOfModules.{w} (RingPresheaf 𝒪)}
    (n : ℕ) {f : F ⟶ G} {g : G ⟶ H} (hfg : f ≫ g = 0) :
    leftTensorHom 𝒪 f n ≫ hom 𝒪 g (n + 1) = 0 := sorry

end PresheafOfModules.SymmetricPower
