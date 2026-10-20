/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetry of the two-variable derived tensor product

@stack 0BYI

The derived braiding is constructed from the universal property of the canonical total
left-derived bifunctor.  Its two natural transformations are explicit data: only the inverse
laws and their consequences remain proof obligations.  In particular, no auxiliary
left-derived instance for the swapped functor is used to choose either morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]

/-- The Koszul braiding on the curried homotopy tensor source. -/
noncomputable def curriedSourceBraiding :
    curriedSourceFunctor (C := C) ≅ (curriedSourceFunctor (C := C)).flip :=
  (Functor.postcompose₂.obj
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)).mapIso
      (BraidedCategory.curriedBraidingNatIso (HomotopyCategory C (up ℤ)))

/-- The Koszul braiding on the uncurried homotopy tensor source. -/
noncomputable def sourceBraiding :
    sourceFunctor (C := C) ≅
      Prod.swap (HomotopyCategory C (up ℤ)) (HomotopyCategory C (up ℤ)) ⋙
        sourceFunctor (C := C) :=
  Functor.uncurry.mapIso (curriedSourceBraiding (C := C)) ≪≫
    Functor.uncurryObjFlip (curriedSourceFunctor (C := C))

/-- The product localization commutes with swapping its two inputs. -/
noncomputable def localizationSwapIso :
    localization (C := C) ⋙
        Prod.swap (DerivedCategory C) (DerivedCategory C) ≅
      Prod.swap (HomotopyCategory C (up ℤ)) (HomotopyCategory C (up ℤ)) ⋙
        localization (C := C) :=
  Iso.refl _

/-- The two-variable derived tensor functor with its inputs exchanged. -/
noncomputable abbrev swappedFunctor [Has (C := C)] :
    DerivedCategory C × DerivedCategory C ⥤ DerivedCategory C :=
  Prod.swap (DerivedCategory C) (DerivedCategory C) ⋙ functor (C := C)

/-- The counit for the swapped derived tensor model, obtained by applying the ordinary counit
at the swapped pair and then the inverse Koszul braiding. -/
noncomputable def swappedCounit [Has (C := C)] :
    localization (C := C) ⋙ swappedFunctor (C := C) ⟶ sourceFunctor (C := C) :=
  (Functor.associator (localization (C := C))
      (Prod.swap (DerivedCategory C) (DerivedCategory C))
      (functor (C := C))).inv ≫
    (Functor.isoWhiskerRight (localizationSwapIso (C := C))
      (functor (C := C))).hom ≫
    (Functor.associator
      (Prod.swap (HomotopyCategory C (up ℤ)) (HomotopyCategory C (up ℤ)))
      (localization (C := C)) (functor (C := C))).hom ≫
    Functor.whiskerLeft
      (Prod.swap (HomotopyCategory C (up ℤ)) (HomotopyCategory C (up ℤ)))
      (counit (C := C)) ≫
    (sourceBraiding (C := C)).inv

/-- The canonical map from the swapped derived tensor bifunctor back to the original one. -/
noncomputable def swapToSelf [Has (C := C)] :
    swappedFunctor (C := C) ⟶ functor (C := C) :=
  (functor (C := C)).leftDerivedLift (counit (C := C)) (qis (C := C))
    (swappedFunctor (C := C)) (swappedCounit (C := C))

/-- The canonical map from derived tensor to derived tensor with the two inputs exchanged. -/
noncomputable def selfToSwap [Has (C := C)] :
    functor (C := C) ⟶ swappedFunctor (C := C) :=
  (Functor.leftUnitor (functor (C := C))).inv ≫
    (Functor.isoWhiskerRight
      (Prod.symmetry (DerivedCategory C) (DerivedCategory C))
      (functor (C := C))).inv ≫
    (Functor.associator
      (Prod.swap (DerivedCategory C) (DerivedCategory C))
      (Prod.swap (DerivedCategory C) (DerivedCategory C))
      (functor (C := C))).hom ≫
    Functor.whiskerLeft (Prod.swap (DerivedCategory C) (DerivedCategory C))
      (swapToSelf (C := C))

/-- The two explicitly constructed swap maps are inverse on the original derived tensor
bifunctor. -/
theorem selfToSwap_swapToSelf [Has (C := C)] :
    selfToSwap (C := C) ≫ swapToSelf (C := C) = 𝟙 (functor (C := C)) := sorry

/-- The two explicitly constructed swap maps are inverse on the swapped derived tensor
bifunctor. -/
theorem swapToSelf_selfToSwap [Has (C := C)] :
    swapToSelf (C := C) ≫ selfToSwap (C := C) = 𝟙 (swappedFunctor (C := C)) := sorry

/-- The canonical derived tensor bifunctor is symmetric in its two inputs. -/
@[stacks 0BYI "derived tensor braiding"]
noncomputable def braiding [Has (C := C)] :
    functor (C := C) ≅ swappedFunctor (C := C) where
  hom := selfToSwap (C := C)
  inv := swapToSelf (C := C)
  hom_inv_id := selfToSwap_swapToSelf (C := C)
  inv_hom_id := swapToSelf_selfToSwap (C := C)

/-- Objectwise derived tensor symmetry, obtained as a component of `braiding`. -/
@[stacks 0BYI "objectwise derived tensor symmetry"]
noncomputable abbrev comm (K L : DerivedCategory C) [Has (C := C)] :
    obj K L ≅ obj L K :=
  (braiding (C := C)).app (K, L)

/-- The map from the swapped model is characterized by the swapped counit. -/
theorem swapToSelf_counit [Has (C := C)] :
    Functor.whiskerLeft (localization (C := C)) (swapToSelf (C := C)) ≫
        counit (C := C) =
      swappedCounit (C := C) := sorry

/-- The derived braiding is compatible with the Koszul braiding through the canonical
derived-tensor counit. -/
theorem braiding_hom_counit [Has (C := C)]
    (X : HomotopyCategory C (up ℤ) × HomotopyCategory C (up ℤ)) :
    (braiding (C := C)).hom.app ((localization (C := C)).obj X) ≫
        (counit (C := C)).app
          ((Prod.swap _ _).obj X) =
      (counit (C := C)).app X ≫ (sourceBraiding (C := C)).hom.app X := sorry

/-- Naturality of objectwise derived tensor symmetry in both variables. -/
@[reassoc (attr := simp)]
theorem comm_hom_naturality [Has (C := C)]
    {K K' L L' : DerivedCategory C} (f : K ⟶ K') (g : L ⟶ L') :
    (functor (C := C)).map (Prod.mkHom f g) ≫ (comm K' L').hom =
      (comm K L).hom ≫ (functor (C := C)).map (Prod.mkHom g f) := sorry

/-- In a symmetric source category, reversing the derived braiding gives the braiding with
the two inputs exchanged. -/
@[simp]
theorem comm_inv [Has (C := C)] (K L : DerivedCategory C) :
    (comm K L).inv = (comm L K).hom := sorry

/-- Applying objectwise derived tensor symmetry twice is the identity. -/
@[reassoc (attr := simp)]
theorem comm_hom_comm_hom [Has (C := C)] (K L : DerivedCategory C) :
    (comm K L).hom ≫ (comm L K).hom = 𝟙 (obj K L) := sorry

end CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor
