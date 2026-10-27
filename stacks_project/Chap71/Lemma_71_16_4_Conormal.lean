/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveBundle.Conormal

/-! # Tensor comparison compatibility for modules on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Pullback preserves the tensor unit of algebraic-space modules. -/
abbrev pullbackMonoidalUnitIso {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) :
    (pullback h).obj (𝟙_ Y.Modules) ≅ 𝟙_ Z.Modules :=
  PullbackTensor.unitIso h

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G` to
`toComm (F ⊗ G)`. -/
abbrev commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((toCommModules Y).obj F).val
        ((toCommModules Y).obj G).val) ⟶
      (toCommModules Y).obj (F ⊗ G)  :=
  RelativeProj.commTensorComparison F G

/-- The oplax comparison `h^*(A ⊗ B) ⟶ h^* A ⊗ h^* B`, the adjunction transpose of the
tensor of units followed by `pushforwardTensorLax`. -/
abbrev pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj (A ⊗ B) ⟶ (pullback h).obj A ⊗ (pullback h).obj B  :=
  RelativeProj.pullbackTensorOplax h A B

end AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.preservesZeroMorphisms_modulesPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (AlgebraicSpace.Modules.pullback f).PreservesZeroMorphisms)
