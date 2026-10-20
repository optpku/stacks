/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Lemma_76_18_1_Thickening
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

/-- The adjoint `𝒪_X`-linear morphism from the pullback of relative differentials to `F`,
obtained by descending a `B`-relative derivation into `a_* F`. -/
def relativeDifferentialDesc_pullback {Y B X : AlgebraicSpace S}
    (hY : Y ⟶ B) (a : X ⟶ Y) {F : X.Modules}
    (D : SheafOfModules.RelativeDerivation.{u + 1, u, u} (inverseImageStructureSheafHom hY)
      ((Modules.pushforward a).obj F)) :
    (Modules.pullback a).obj
      (relativeDifferentials.{u + 1, u, u} (inverseImageStructureSheafHom hY)) ⟶ F :=
  ((Modules.pullbackPushforwardAdjunction a).homEquiv _ _).symm
    (relativeDifferentialDesc.{u + 1, u, u} (inverseImageStructureSheafHom hY) D)

variable {B X X' Y : AlgebraicSpace S}
variable (hY : Y ⟶ B) (a : X ⟶ Y) (iX : X ⟶ X') [IsFirstOrderThickening iX]
variable (D : SheafOfModules.RelativeDerivation.{u + 1, u, u} (inverseImageStructureSheafHom hY)
  ((Modules.pushforward a).obj (conormalSheaf iX)))

/- 76.17.1.1: the `B`-relative derivation `D` into `a_* C_{X/X'}` factors through
the universal relative differential and its descended `𝒪_Y`-linear map `θ`.
The relative differential sheaf here is that of the inverse-image structure map
`inverseImageStructureSheafHom hY`, namely `Ω_{Y/B}`, not a different differential object.
Postcomposition applies the universal differential first and `θ` second. -/
@[stacks 0619] #check
  (SheafOfModules.RingedSite.relativeDifferentialDesc_fac.{u + 1, u, u}
      (inverseImageStructureSheafHom hY) D :
    (relativeDifferential.{u + 1, u, u} (inverseImageStructureSheafHom hY)).postcomp
      (relativeDifferentialDesc.{u + 1, u, u} (inverseImageStructureSheafHom hY) D).val = D)

#check
  (relativeDifferentialDesc_pullback hY a D :
    (Modules.pullback a).obj
      (relativeDifferentials.{u + 1, u, u} (inverseImageStructureSheafHom hY)) ⟶ conormalSheaf iX)

#check
  (Equiv.apply_symm_apply
      ((Modules.pullbackPushforwardAdjunction a).homEquiv
        (relativeDifferentials.{u + 1, u, u} (inverseImageStructureSheafHom hY)) (conormalSheaf iX))
      (relativeDifferentialDesc.{u + 1, u, u} (inverseImageStructureSheafHom hY) D) :
    (Modules.pullbackPushforwardAdjunction a).homEquiv
        (relativeDifferentials.{u + 1, u, u} (inverseImageStructureSheafHom hY)) (conormalSheaf iX)
        (relativeDifferentialDesc_pullback hY a D) =
      relativeDifferentialDesc.{u + 1, u, u} (inverseImageStructureSheafHom hY) D)

end AlgebraicGeometry.AlgebraicSpace.Hom
