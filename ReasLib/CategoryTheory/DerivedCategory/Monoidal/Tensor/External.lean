/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Presheaf.Tensor
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.CategoryTheory.Monoidal.ExternalProduct.Presheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Heterogeneous derived external tensor

For module-valued presheaves, the product-site tensor is obtained by exact pullback along the two
projections followed by the canonical two-variable derived tensor on the product presheaf
category.  The construction is a genuine bifunctor.  Its underived model is the naturally
isomorphic projection-pullback presentation
`CategoryTheory.MonoidalCategory.ExternalProduct.tensorPullback`.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe q₁ q₂ q₁₂ u₁ v₁ u₂ v₂ w

namespace CategoryTheory.DerivedCategory.DerivedTensor.External

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {B : Type w} [CommRing B]
variable [HasDerivedCategory.{q₁} (ModuleCat.Presheaf C₁ B)]
variable [HasDerivedCategory.{q₂} (ModuleCat.Presheaf C₂ B)]
variable [HasDerivedCategory.{q₁₂} (ModuleCat.Presheaf (C₁ × C₂) B)]

/-- Exact inverse image along the first projection on derived presheaves. -/
@[stacks 08QB "derived first projection inverse image"]
noncomputable abbrev leftDerived :
    DerivedCategory (ModuleCat.Presheaf C₁ B) ⥤
      DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (MonoidalCategory.ExternalProduct.left
    (C₁ := C₁) (C₂ := C₂) (A := ModuleCat B)).mapDerivedCategory

/-- Exact inverse image along the second projection on derived presheaves. -/
@[stacks 08QB "derived second projection inverse image"]
noncomputable abbrev rightDerived :
    DerivedCategory (ModuleCat.Presheaf C₂ B) ⥤
      DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (MonoidalCategory.ExternalProduct.right
    (C₁ := C₁) (C₂ := C₂) (A := ModuleCat B)).mapDerivedCategory

/-- Simultaneous derived inverse image along the two projections. -/
@[stacks 08QB "product of the derived projection inverse images"]
noncomputable abbrev pullback :
    (DerivedCategory (ModuleCat.Presheaf C₁ B) ×
      DerivedCategory (ModuleCat.Presheaf C₂ B)) ⥤
        DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) ×
          DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (leftDerived (C₁ := C₁) (C₂ := C₂) (B := B)).prod
    (rightDerived (C₁ := C₁) (C₂ := C₂) (B := B))

/-- The heterogeneous derived external tensor bifunctor. -/
@[stacks 08QB "derived external tensor bifunctor"]
noncomputable abbrev functor :
    (DerivedCategory (ModuleCat.Presheaf C₁ B) ×
      DerivedCategory (ModuleCat.Presheaf C₂ B)) ⥤
        DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  pullback (C₁ := C₁) (C₂ := C₂) (B := B) ⋙
    DerivedCategory.DerivedTensor.Bifunctor.functor

/-- The fixed-left view of the derived external tensor bifunctor. -/
@[stacks 08QB "fixed-left derived external tensor functor"]
noncomputable abbrev leftFunctor
    (K₁ : DerivedCategory (ModuleCat.Presheaf C₁ B)) :
    DerivedCategory (ModuleCat.Presheaf C₂ B) ⥤
      DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (Functor.curry.obj (functor (C₁ := C₁) (C₂ := C₂) (B := B))).obj K₁

/-- The fixed-right view of the derived external tensor bifunctor. -/
@[stacks 08QB "fixed-right derived external tensor functor"]
noncomputable abbrev rightFunctor
    (K₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)) :
    DerivedCategory (ModuleCat.Presheaf C₁ B) ⥤
      DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (Functor.curry.obj (functor (C₁ := C₁) (C₂ := C₂) (B := B))).flip.obj K₂

/-- The heterogeneous derived external tensor on two derived presheaves. -/
@[stacks 08QB "heterogeneous derived external tensor for a product category"]
noncomputable abbrev obj
    (K₁ : DerivedCategory (ModuleCat.Presheaf C₁ B))
    (K₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)) :
    DerivedCategory (ModuleCat.Presheaf (C₁ × C₂) B) :=
  (functor (C₁ := C₁) (C₂ := C₂) (B := B)).obj (K₁, K₂)

/-- The action of the derived external tensor on a pair of morphisms. -/
@[stacks 08QB "derived external tensor morphism"]
noncomputable abbrev map {K₁ L₁ : DerivedCategory (ModuleCat.Presheaf C₁ B)}
    {K₂ L₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
    obj K₁ K₂ ⟶ obj L₁ L₂ :=
  (functor (C₁ := C₁) (C₂ := C₂) (B := B)).map (Prod.mkHom f₁ f₂)

/-- Derived external tensor preserves composition simultaneously in both variables. -/
@[stacks 08QB "derived external tensor composition"]
theorem map_comp {K₁ L₁ M₁ : DerivedCategory (ModuleCat.Presheaf C₁ B)}
    {K₂ L₂ M₂ : DerivedCategory (ModuleCat.Presheaf C₂ B)}
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁)
    (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    map f₁ f₂ ≫ map g₁ g₂ = map (f₁ ≫ g₁) (f₂ ≫ g₂) := sorry

end CategoryTheory.DerivedCategory.DerivedTensor.External
