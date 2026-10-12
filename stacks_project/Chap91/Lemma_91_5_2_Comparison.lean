/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import stacks_project.Chap91.Lemma_91_5_1_IdealMul
public import stacks_project.Chap91.Situation_91_3_1_Comparison

/-!
# Canonical maps `ℐ ⊗ F ⟶ ℐ F'` and `f^* 𝒥 ⊗ F ⟶ ℐ F'`

Along a first-order thickening, the kernel-ideal action on `F'` pulls back to an
`𝒪_X`-map `ℐ ⊗ F ⟶ ℐ F'`. A morphism of first-order thickenings then supplies the
canonical comparison `f^* 𝒥 ⊗ F ⟶ ℐ F'` by tensoring `sourceIdealMap` with `F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

/-- The `𝒪_X`-map `ℐ ⊗ F ⟶ ℐ F'` obtained by pulling back the kernel-ideal action
`ℐ ⊗ F' ⟶ ℐ F'` along a first-order thickening `i`. -/
def actionToIdealMulRestrict (F' : X'.Modules) :
    idealModule i ⊗ (i ^*).obj F' ⟶ idealMulRestrict i F' :=
  (Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) F').hom ≫
    (i ^*).map (actionToIdealMul i F')

/-- `actionToIdealMulRestrict` is the monoidal comparison of pullback followed by inverse
image of `actionToIdealMul`. -/
theorem actionToIdealMulRestrict_comp (F' : X'.Modules) :
    actionToIdealMulRestrict i F' =
      (Functor.Monoidal.μIso (pullback i) (kernelIdealSheaf i) F').hom ≫
        (i ^*).map (actionToIdealMul i F') := sorry

end AlgebraicGeometry.RingedSpace.Hom

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

/-- The canonical `𝒪_X`-map `f^* 𝒥 ⊗ F ⟶ ℐ F'` along a morphism of first-order
thickenings, obtained by tensoring `sourceIdealMap` with `F` and composing with
`actionToIdealMulRestrict`. -/
def sourceIdealMulMap (g : T ⟶ U) (F' : T.right.Modules) :
    (g.left ^*).obj (RingedSpace.Hom.idealModule U.hom) ⊗ (T.hom^*).obj F' ⟶
      RingedSpace.Hom.idealMulRestrict T.hom F' :=
  tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F')) ≫
    RingedSpace.Hom.actionToIdealMulRestrict T.hom F'

/-- `sourceIdealMulMap` factors as `tensorHom (sourceIdealMap g) (𝟙 F)` followed by
`actionToIdealMulRestrict`. -/
theorem sourceIdealMulMap_comp (g : T ⟶ U) (F' : T.right.Modules) :
    sourceIdealMulMap g F' =
      tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F')) ≫
        RingedSpace.Hom.actionToIdealMulRestrict T.hom F' := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
