/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Affine

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped AlgebraicGeometry

noncomputable section

universe u

/- This compatibility bridge re-exports the affine eta API from its mathematical owner. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.Eta.affineSectionsIso :
  ∀ {X : Scheme.{u}} (D : X.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (K : CochainComplex X.Modules ℤ) [∀ i : ℤ, (K.X i).IsQuasicoherent]
    [AlgebraicGeometry.RingedSpace.IdealSheaf.IsActionMono.Complex D.toSubobject K]
    (U : X.affineOpens) (f : Γ(X, U.1)) (hf : D.ideal U = Ideal.span {f}),
    CochainComplex.BerthelotOgus.Int.eta f
        (AlgebraicGeometry.Scheme.IdealSheafData.Eta.affineSectionsComplex U K)
        (AlgebraicGeometry.Scheme.IdealSheafData.Eta.affineSectionsRegular D K U f hf) ≅
      AlgebraicGeometry.Scheme.IdealSheafData.Eta.affineSectionsComplex U
        (AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.complex D.toSubobject K))
