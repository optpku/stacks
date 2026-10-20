/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Cofiltered
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Sections
public import ReasLib.RingTheory.Henselian.Henselization.Presentation.PointedEtale

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary

/-- A henselization of the stalk at a point is isomorphic to the filtered colimit of the
global-section rings of the elementary étale neighborhoods of that point. -/
theorem nonempty_henselizationIsoColimit (S : Scheme.{u}) (s : S) (Rh : Type u)
    [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of Rh) ≅
        colimit (sections S s)) := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary
