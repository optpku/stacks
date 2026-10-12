/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
import stacks_project.Chap76.Lemma_76_15_8_Comparison

/-!
# Identity-square conormal comparison for two formally unramified morphisms

The first arrow of Lemma 76.15.14 is identity-pullback transport of the
Lemma 76.15.8 conormal map on the identity square over `Z`. This module
imports that owner only; it does not import Lemma 76.15.13.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
  (idealSheaf idealSheafSubobject)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
namespace Transitivity

variable {S : Scheme.{u}}

/-- The coborder expansion of `C_{Z/X}`, which is definitionally
`Hom.conormalSheaf` when that owner is in the environment. -/
noncomputable abbrev conormal {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i] :
    Z.Modules :=
  (Modules.pullback (IsImmersion.liftCoborder i)).obj
    (Modules.quotientByIdeal (idealSheafSubobject (IsImmersion.liftCoborder i))
      (idealSheaf (IsImmersion.liftCoborder i)))

variable {X Y Z ZX ZY : AlgebraicSpace S}

/-- The first arrow `C_{Z/Y} ⟶ C_{Z/X}` of the two-unramified-morphisms sequence,
as identity-pullback transport of the Lemma 76.15.8 conormal comparison. -/
noncomputable def projection (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y)
    (f : X ⟶ Y) [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    conormal iY ⟶ conormal iX :=
  (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormal iY) ≫
    IsUniversalFirstOrder.conormalMap iX fX iY fY (𝟙 Z) f sq

/-- `projection` is identity-pullback transport of the Lemma 76.15.8 conormal map
of the identity square on `Z`. -/
private theorem projection_eq (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY)
    (fY : ZY ⟶ Y) (f : X ⟶ Y)
    [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
    [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
    (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f) :
    projection iX fX iY fY f sq =
      (SmallEtaleModuleGlueing.modulesPullbackId Z).inv.app (conormal iY) ≫
        IsUniversalFirstOrder.conormalMap iX fX iY fY (𝟙 Z) f sq :=
  sorry

end Transitivity
end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials
