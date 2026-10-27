/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.IsoClass

/-!
# Identity fillings and coefficient transport for compatible automorphisms

Kernel identifications transport relative differential morphisms to perturbations
of the identity filling of a first-order solution.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/-- Transport a map `Ω[f] ⟶ G` to the perturb argument of the identity cube. -/
def homToPerturb (S : Solution t f G c) (α : Ω[f] ⟶ G) :
    Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i) :=
  α ≫ S.kernelIso.inv ≫
    (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S.i) ≫
    ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S.i))

/-- Unfolding of `homToPerturb` along `kernelIso` and the identity pullback unit. -/
theorem homToPerturb_eq (S : Solution t f G c) (α : Ω[f] ⟶ G) :
    homToPerturb t f G c S α =
      α ≫ S.kernelIso.inv ≫
        (pullbackPushforwardAdjunction (𝟙 X)).unit.app (idealModule S.i) ≫
        ((𝟙 X) _*).map ((pullbackIdIso X).hom.app (idealModule S.i)) :=
  rfl

/-- Reverse transport from the perturb argument of the identity cube to `Ω[f] ⟶ G`. -/
def perturbToHom (S : Solution t f G c)
    (α : Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i)) : Ω[f] ⟶ G :=
  (pullbackIdIso X).inv.app Ω[f] ≫
    ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv Ω[f] (idealModule S.i)).symm α ≫
    S.kernelIso.hom

/-- Unfolding of `perturbToHom` along the identity pullback adjunction and `kernelIso`. -/
theorem perturbToHom_eq (S : Solution t f G c)
    (α : Ω[f] ⟶ ((𝟙 X) _*).obj (idealModule S.i)) :
    perturbToHom t f G c S α =
      (pullbackIdIso X).inv.app Ω[f] ≫
        ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv Ω[f] (idealModule S.i)).symm α ≫
        S.kernelIso.hom :=
  rfl

/-- The identity automorphism of a solution, as a fitting map of the identity diagram. -/
def idFitting (S : Solution t f G c) : Solution.Fitting S S :=
  @FittingMap.mk _ _ _ _ _ _ _ _
    S.i f S.f' t S.i f S.f' t (𝟙 X) (𝟙 _) (𝟙 S')
    S.i_isFirstOrder inferInstance S.i_isFirstOrder inferInstance (compare S S)
    (hom := 𝟙 S.space) (comm_top := sorry) (comm_right := sorry) (induces := sorry)

/-- The underlying morphism of `idFitting` is the identity on the middle ringed space. -/
theorem idFitting_hom (S : Solution t f G c) :
    @FittingMap.hom _ _ _ _ _ _ _ _
      S.i f S.f' t S.i f S.f' t (𝟙 X) (𝟙 _) (𝟙 S')
      S.i_isFirstOrder inferInstance S.i_isFirstOrder inferInstance
      (compare S S) (idFitting t f G c S) = 𝟙 S.space :=
  rfl

end AlgebraicGeometry.RingedSpace.Thickening
