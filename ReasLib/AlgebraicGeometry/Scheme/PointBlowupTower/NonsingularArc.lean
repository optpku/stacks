/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FormalArc
public import ReasLib.AlgebraicGeometry.Scheme.PointBlowupTower
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Nonsingular arcs realizing point blowup towers

This file states the realization of compatible point blowup towers by nonsingular formal arcs.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PointBlowupTower

/-- A locally Noetherian point-blowup tower preserving residue fields and sharing an exceptional
generator is realized by a nonsingular formal arc with compatible stage lifts. -/
theorem exists_nonsingularFormalArc {X : Scheme.{u}} [IsLocallyNoetherian X]
    (p : closedPoints X) (S : PointBlowupTower X p)
    (h_residue : S.PreservesResidueFields)
    (h_generator : S.HasCommonExceptionalGenerator) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : IsCompleteLocalRing R)
      (A : FormalArc X p R)
      (L : S.Lift A.hom (IsLocalRing.closedPoint R)), A.IsNonsingular := sorry

end AlgebraicGeometry.Scheme.PointBlowupTower
