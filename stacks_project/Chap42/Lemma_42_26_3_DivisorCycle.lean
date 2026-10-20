/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Pullback

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry

/- Compatibility checks for the reusable Weil-divisor cycle API. -/
#check (AlgebraicGeometry.WeilDivisor.genericPointTermsLocallyFinite :
  ∀ {X : Scheme.{u}} (D : Div(X)),
    LocallyFinite fun Z : PrimeDivisor X ↦
      (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        Z.genericPoint (D.coeff Z)).support)

#check (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle :
  ∀ {X : Scheme.{u}}, Div(X) → AlgebraicCycle X ℤ)

#check (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_apply :
  ∀ {X : Scheme.{u}} (D : Div(X)) (x : X),
    AlgebraicGeometry.WeilDivisor.toAlgebraicCycle D x =
      ∑ᶠ Z : PrimeDivisor X,
        (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
          Z.genericPoint (D.coeff Z)) x)

#check (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_zsmul :
  ∀ {X : Scheme.{u}} (n : ℤ) (D : Div(X)),
    AlgebraicGeometry.WeilDivisor.toAlgebraicCycle (n • D) =
      n • AlgebraicGeometry.WeilDivisor.toAlgebraicCycle D)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionDivisorCycle :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ),
    s ≠ 0 → AlgebraicCycle X ℤ)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionDivisorCycle_def :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0),
    AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionDivisorCycle X ℒ s hs =
      AlgebraicGeometry.WeilDivisor.toAlgebraicCycle
        (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor X ℒ s hs))

#check
  (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackSections_ne_zero_of_isDominant :
    ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
      (f : X ⟶ Y) [IsDominant f]
      (ℒ : Y.Modules) [Scheme.Modules.Invertible ℒ]
      (s : Y.toLocallyRingedSpace.meromorphicSections ℒ), s ≠ 0 →
      LocallyRingedSpace.Hom.pullbackMeromorphicSections f.toLRSHom
        (Scheme.Hom.MeromorphicFunction.pullbackDefined_of_isIntegral_of_isDominant f)
        ℒ s ≠ 0)

end AlgebraicGeometry
