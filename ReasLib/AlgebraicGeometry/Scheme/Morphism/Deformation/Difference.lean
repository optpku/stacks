/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal.SquareZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.SquareZeroExtension

/-!
# Differences of morphisms between first-order thickenings

For two ambient maps inducing the same map on conormal sheaves, their difference factors
through a relative derivation on the reduced target.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- The additive difference between two presentation maps, oriented as the first ambient map
minus the second. -/
noncomputable def presentationDifference {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' b' : X' ⟶ Y'} (sqA : CommSq a i j a') (sqB : CommSq a i j b') :=
  let pA : IsFirstOrderThickening.presentationSheaf j ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
        (IsFirstOrderThickening.presentationSheaf i) := Conormal.presentationMap sqA
  let pB : IsFirstOrderThickening.presentationSheaf j ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
        (IsFirstOrderThickening.presentationSheaf i) := Conormal.presentationMap sqB
  SquareZeroExtension.additiveDifference
    (J := Opens.grothendieckTopology Y)
    (B := IsFirstOrderThickening.presentationSheaf j)
    (A := (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
      (IsFirstOrderThickening.presentationSheaf i)) pB pA

/-- The presentation difference evaluates sectionwise as the first presentation map minus the
second. -/
theorem presentationDifference_apply {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y}
    {a' b' : X' ⟶ Y'} (sqA : CommSq a i j a') (sqB : CommSq a i j b')
    (U : (Opens Y)ᵒᵖ) (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U) :
    (presentationDifference sqA sqB).hom.app U x =
      (Conormal.presentationMap sqA).hom.app U x -
        (Conormal.presentationMap sqB).hom.app U x := sorry

/-- Two morphisms of first-order thickenings over a scheme with a common restriction and equal
conormal maps differ by a relative derivation into the pushforward conormal sheaf; the conormal
inclusion recovers the difference of the ambient presentation maps sectionwise. -/
theorem exists_differenceDerivation (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    (a' b' : X' ⟶ Y') [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S] [b'.IsOver S]
    (sqA : CommSq a i j a') (sqB : CommSq a i j b')
    (hconormal : Conormal.map sqA = Conormal.map sqB) :
    ∃ D : RingedSpace.Hom.derivations (Y ↘ S).toShHom
        ((Scheme.Modules.pushforward a).obj (Scheme.Hom.conormalSheaf i)),
      ∀ (U : (Opens Y)ᵒᵖ)
        (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U),
        (presentationDifference sqA sqB).hom.app U x =
          (SquareZeroExtension.conormalInclusion
            (IsFirstOrderThickening.presentationProjection i)
            (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
              ((Opens.map a.base).op.obj U)
              (D.d ((IsFirstOrderThickening.presentationProjection j).hom.app U x)) := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
