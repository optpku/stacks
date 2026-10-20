/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules.ClosedSubset
open SheafOfModules.ClosedSubset.SupportedDerived

noncomputable section

universe u

/- Remark 36.6.6: the canonical factor from the derived principal-open Čech complex through
closed-support local cohomology forms the stated commutative triangle, naturally in the module. -/
@[stacks 0G7L] #check
  (ModuleCech.ofSectionsToLocalCohomology_triangle :
    ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules),
      (ModuleCech.ofSectionsToLocalCohomology f).app ℱ ≫
        (adjunction
          X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).counit.app
            ((ModuleCech.moduleToDerived X).obj ℱ) =
        (ModuleCech.ofSectionsProjectionDerived f).app ℱ)

#check
  (ModuleCech.ofSectionsDerived_isSupportedOn :
    ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules),
      RingedSpace.ModuleDerived.IsSupportedOn
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ)
        (ModuleCech.ofSectionsZeroLocus f))

#check
  (ModuleCech.ofSectionsToLocalCohomology :
    ∀ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)),
      ModuleCech.ofSectionsDerivedFunctor f ⟶
        ModuleCech.moduleToDerived X ⋙
          coreflector
            X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⋙
          inclusion
            X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f))

end
