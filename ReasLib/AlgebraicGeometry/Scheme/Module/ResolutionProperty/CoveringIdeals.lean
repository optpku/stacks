/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- For a finite affine open cover with finite-type ideal sheaves supported on the respective
closed complements, a scheme has the resolution property exactly when every covering ideal is
an epimorphic quotient of a finite locally free module. -/
theorem hasResolutionProperty_iff_coveringIdealQuotients {X : Scheme.{u}} {m : ℕ}
    (U : Fin m → X.affineOpens)
    (hU : TopologicalSpace.IsOpenCover (fun j ↦ (U j : X.Opens)))
    (I : Fin m → X.IdealSheafData) (hI : ∀ j, (I j).IsFiniteType)
    (hIU : ∀ j, (I j).support = (U j : X.Opens).compl) :
    HasResolutionProperty X ↔
      ∀ j, ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
        (q : E ⟶ ((I j).toModule : X.Modules)), Epi q := sorry

end AlgebraicGeometry.Scheme
