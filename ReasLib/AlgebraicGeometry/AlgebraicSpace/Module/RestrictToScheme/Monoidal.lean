/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPower

/-! # Lax monoidal restriction of algebraic-space modules to schemes -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}} (Z : Over S)

/-- Restriction to a scheme is lax monoidal through the sectionwise tensor comparison
and the inverse of the monoidal unit comparison. -/
instance laxMonoidal : (restrictToScheme Z).LaxMonoidal := by
  let F := restrictToScheme Z
  let ε : 𝟙_ Z.left.Modules ⟶ F.obj (𝟙_ (ofOver Z).Modules) :=
    (restrictMonoidalUnitIso Z).inv
  let μ := fun A B : (ofOver Z).Modules ↦ restrictTensorLax A B
  have laws :
      (∀ {A B A' B' : (ofOver Z).Modules} (f : A ⟶ B) (g : A' ⟶ B'),
        (F.map f ⊗ₘ F.map g) ≫ μ B B' = μ A A' ≫ F.map (f ⊗ₘ g)) ∧
      (∀ A B C : (ofOver Z).Modules,
        (μ A B ⊗ₘ 𝟙 (F.obj C)) ≫ μ (A ⊗ B) C ≫ F.map (α_ A B C).hom =
          (α_ (F.obj A) (F.obj B) (F.obj C)).hom ≫
            (𝟙 (F.obj A) ⊗ₘ μ B C) ≫ μ A (B ⊗ C)) ∧
      (∀ A : (ofOver Z).Modules,
        (λ_ (F.obj A)).hom = (ε ⊗ₘ 𝟙 (F.obj A)) ≫ μ (𝟙_ (ofOver Z).Modules) A ≫
          F.map (λ_ A).hom) ∧
      (∀ A : (ofOver Z).Modules,
        (ρ_ (F.obj A)).hom = (𝟙 (F.obj A) ⊗ₘ ε) ≫ μ A (𝟙_ (ofOver Z).Modules) ≫
          F.map (ρ_ A).hom) := sorry
  exact Functor.LaxMonoidal.ofTensorHom ε μ laws.1 laws.2.1 laws.2.2.1 laws.2.2.2

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
