/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Inertia

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L]

#check (galoisSpec X L :
  (L ≃ₐ[X.functionField] L) →
    (Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L)))

#check (map_comp_galoisSpec X L :
  ∀ σ : L ≃ₐ[X.functionField] L, galoisSpec X L σ ≫ map X L = map X L)

#check (galoisHom_factor X L :
  ∀ σ : L ≃ₐ[X.functionField] L,
    map X L =
      (galoisSpec X L σ ≫ (map X L).toNormalization) ≫ (map X L).fromNormalization)

#check (galoisHom X L :
  (L ≃ₐ[X.functionField] L) →
    ((map X L).normalization ⟶ (map X L).normalization))

#check (inertia X L : (map X L).normalization → Subgroup (L ≃ₐ[X.functionField] L))

#check (mem_inertia_iff X L :
  ∀ (y : (map X L).normalization) (σ : L ≃ₐ[X.functionField] L),
    σ ∈ inertia X L y ↔
      galoisHom X L σ y = y ∧
        ∀ hy : galoisHom X L σ y = y,
          (galoisHom X L σ).residueFieldMap y =
            eqToHom (congrArg (Scheme.residueField (map X L).normalization) hy))

#check (inertia_eq_bot_iff X L :
  ∀ y : (map X L).normalization,
    inertia X L y = ⊥ ↔ ∀ σ : L ≃ₐ[X.functionField] L, σ ∈ inertia X L y → σ = 1)

end AlgebraicGeometry.Scheme.FunctionFieldExtension
