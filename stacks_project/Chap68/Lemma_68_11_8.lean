/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Henselization
public import ReasLib.RingTheory.Henselian.Henselization
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing

/-!
# Henselian local rings of decent algebraic spaces along elementary neighbourhoods

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

/-- Lemma 68.11.8: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `U : Elementary X x` be an elementary étale neighbourhood
`(U, u) ⟶ (X, x)`. Then `henselianLocalRing X x` equals a henselization of the
local ring `(scheme U.obj).presheaf.stalk (point U.obj)` of `U` at `u`. The
identification is a `CommRingCat` isomorphism after `CommRingCat.universeLift`. -/
@[stacks 0EMY]
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

/-- The colimit of global-section rings of elementary étale neighbourhoods of
`(scheme U.obj, point U.obj)` is isomorphic to `henselianLocalRingCat X x`. -/
theorem henselianLocalRingCat.nonempty_iso_schemeSections (U : Elementary X x) :
    Nonempty
      (colimit (sections (scheme U.obj) (point U.obj)) ≅
        henselianLocalRingCat X x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
