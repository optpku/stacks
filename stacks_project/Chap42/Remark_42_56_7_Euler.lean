/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Euler

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

#check (AlgebraicGeometry.Scheme.K0WithSupport.toCoherent :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (T : Set X),
    K0WithSupport X T →+ K0'WithSupport X T)

end AlgebraicGeometry.Scheme.K0WithSupport
