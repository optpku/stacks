/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.IdealSurjection

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Remark 42.29.2: an invertible module `N` on a locally principal closed subscheme `D`
and an epimorphism from the dual of `N` to the pulled-back ideal sheaf determine a generalized
Gysin map `Z_(k + 1)(X) → CH_k(D)`. -/
@[stacks 0B70] #check (AlgebraicGeometry.Scheme.IdealSheafData.gysin :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (D : X.IdealSheafData)
    [IsLocallyPrincipalClosedSubscheme D.subschemeι]
    (N : D.subscheme.Modules) [Scheme.Modules.Invertible N]
    (sigma : Scheme.Modules.dual N ⟶
      (Scheme.Modules.pullback D.subschemeι).obj
        (RingedSpace.Hom.kernelIdealSheaf D.subschemeι.toShHom))
    [Epi sigma] (k : ℤ),
    CycleGroup X (p.relativeDimensionFunction delta) (k + 1) →+
      @ChowGroup D.subscheme
        (@Scheme.IdealSheafData.subschemeIsLocallyNoetherian X
          (LocallyOfFiniteType.isLocallyNoetherian p) D)
        ((D.subschemeι ≫ p).relativeDimensionFunction delta) inferInstance k)
