/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DeRham.Pushforward
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Lemma 50.3.3: If `p : X ⟶ S` is proper and `S` is locally Noetherian, then the derived
pushforward of the relative de Rham complex has coherent cohomology on `S`. -/
@[stacks 0FLY] #check
  (AlgebraicGeometry.Scheme.DeRham.pushforwardDerivedComplex_isCoherent :
    ∀ {X S : Scheme.{u}} (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p],
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent S.toRingedSpace.ringCatSheaf)
        ((RingedSpace.moduleDerivedPushforward
          (ModuleCech.relativeSpaceMap p.toLRSHom.toShHom)).obj
          ((CochainComplex.Nat.toDerived
            (ModuleCech.relativeSpace p.toLRSHom.toShHom).Modules).obj
            (RingedSpace.DeRham.complex p.toLRSHom.toShHom))))

end AlgebraicGeometry.Scheme.DeRham
