/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Cohomology

/-! # Derived Hom in a chosen closed presentation -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)]

/-- Target object `ihom(E, Q(G ⊗ f^* F))`, the derived internal-Hom model of
`Ext^i_{𝒪_X}(E, G ⊗ f^* F)`. -/
def extTarget (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    ModuleDerived X :=
  (ihomOf H E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F))

/-- `extTarget` is the derived internal Hom from `E` into `Q.obj (G ⊗ f^* F)`. -/
theorem extTarget_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (F : Modules B) :
    extTarget f H E G F =
      (ihomOf H E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F)) :=
  rfl

/-- Strong monoidality of the homotopy localization of `D(𝒪_Y)`, used to compare
fixed-right derived tensor with the ambient monoidal tensor on `ModuleDerived Y`. -/
abbrev localizationMonoidal (Y : AlgebraicSpace S)
    [MonoidalCategory (ModuleDerived Y)] :=
  (DerivedTensor.Right.localization :
    HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y).Monoidal

/-- Induced map on `ihom(E, Q(G ⊗ f^* -))` from a morphism of modules on `B`. -/
def extTargetMap (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F') :
    extTarget f H E G F ⟶ extTarget f H E G F' :=
  (ihomOf H E).map
    (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom (𝟙 G)
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
          ((Modules.pullback f).map φ))))

/-- Shift compatibility of `ihomOf H E` as the right adjoint of `tensorLeft E`. -/
noncomputable instance ihomOf_commShift (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) [(tensorLeft E).CommShift ℤ] :
    (ihomOf H E).CommShift ℤ :=
  (adjunctionOf H E).rightAdjointCommShift ℤ

/-- Connecting map on `Ext^i_{𝒪_X}(E, G ⊗ f^* -)` attached to a short exact sequence of
modules on `B`. -/
def extTargetδ (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ)
    [(tensorLeft E).CommShift ℤ] :
    cohomologyAb X (extTarget f H E G s.X₃) i ⟶
      cohomologyAb X (extTarget f H E G s.X₁) (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
      ((ihomOf H E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
    i (i + 1) rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
