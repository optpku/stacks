/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization

/-!
# Henselian local rings along elementary étale neighbourhoods

The henselian local ring of a decent algebraic space at a point identifies with the
henselization of the Zariski local ring of any elementary étale neighbourhood.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicSpace EtaleNeighborhood
open CategoryTheory CategoryTheory.Limits
open Scheme.EtaleNeighborhood.Elementary (sections)

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X}

/-- The colimit of global-section rings of elementary étale neighbourhoods of
`(scheme U.obj, point U.obj)` is isomorphic to `henselianLocalRingCat X x`. -/
theorem henselianLocalRingCat.nonempty_iso_schemeSections (U : Elementary X x) :
    Nonempty
      (colimit (sections (scheme U.obj) (point U.obj)) ≅
        henselianLocalRingCat X x) :=
  sorry

/-- A henselization of the Zariski stalk of an elementary étale neighbourhood of a
point of a decent algebraic space is isomorphic, after universe lift, to the
henselian local ring of the algebraic space at that point. -/
theorem henselianLocalRing.nonempty_iso_henselization (U : Elementary X x)
    (Rh : Type u) [CommRing Rh]
    [Algebra ((scheme U.obj).presheaf.stalk (point U.obj)) Rh]
    [IsHenselizationOf ((scheme U.obj).presheaf.stalk (point U.obj)) Rh] :
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of Rh) ≅
        henselianLocalRingCat X x) :=
  sorry

/-- A henselization of the Zariski stalk of an elementary étale neighbourhood is
ring-equivalent, after `ULift`, to the henselian local ring of the algebraic space. -/
theorem henselianLocalRing.nonempty_ringEquiv_henselization (U : Elementary X x)
    (Rh : Type u) [CommRing Rh]
    [Algebra ((scheme U.obj).presheaf.stalk (point U.obj)) Rh]
    [IsHenselizationOf ((scheme U.obj).presheaf.stalk (point U.obj)) Rh] :
    Nonempty (ULift.{u + 1} Rh ≃+* henselianLocalRing X x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
