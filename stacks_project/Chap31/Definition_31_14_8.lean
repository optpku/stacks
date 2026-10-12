/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
import StacksCheckRecall

@[expose] public section

/-!
# Definition 31.14.8

@stack 02OQ

The canonical owner is `AlgebraicGeometry.Scheme.zeroScheme`.
-/

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

/- Definition 31.14.8: For a scheme `X`, an invertible module sheaf `ℒ`, and a global
section `s`, the zero scheme `Z(s)` is the closed subscheme cut out by the ideal sheaf
defined by the image of the dual section. -/
@[stacks 02OQ] #check
  (@AlgebraicGeometry.Scheme.zeroScheme X
      (AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X) :
    (ℒ : X.Modules) →
      [CategoryTheory.Functor.IsEquivalence
        (CategoryTheory.MonoidalCategory.tensorRight ℒ)] →
          (s : ℒ.sections) → AlgebraicGeometry.Scheme.{u})

#check
  (@AlgebraicGeometry.Scheme.dualSectionHom X :
    (ℒ : X.Modules) →
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] →
        (s : ℒ.sections) →
          (CategoryTheory.ihom ℒ).obj
              (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
            (SheafOfModules.unit X.ringCatSheaf : X.Modules))

#check
  (@AlgebraicGeometry.Scheme.zeroIdealSubobject X :
    (ℒ : X.Modules) →
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] →
        (s : ℒ.sections) → X.IdealSubobject)

#check
  (@AlgebraicGeometry.Scheme.zeroIdealSheaf_toSubobject X :
    (ℒ : X.Modules) →
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] →
        (s : ℒ.sections) →
          (AlgebraicGeometry.Scheme.zeroIdealSheaf ℒ s).toSubobject =
            AlgebraicGeometry.Scheme.zeroIdealSubobject ℒ s)

#check
  (@AlgebraicGeometry.Scheme.zeroIdealSheaf X
      (AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X) :
    (ℒ : X.Modules) →
      [CategoryTheory.Functor.IsEquivalence
        (CategoryTheory.MonoidalCategory.tensorRight ℒ)] →
          (s : ℒ.sections) → X.IdealSheafData)

#check
  (@AlgebraicGeometry.Scheme.zeroSchemeι X
      (AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X) :
    (ℒ : X.Modules) →
      [CategoryTheory.Functor.IsEquivalence
        (CategoryTheory.MonoidalCategory.tensorRight ℒ)] →
          (s : ℒ.sections) → AlgebraicGeometry.Scheme.zeroScheme ℒ s ⟶ X)
