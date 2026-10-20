/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Order
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.IrreducibleComponents

/-! # Local finiteness of the vanishing and poles of rational units -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The prime divisors where a rational unit fails to lie in the henselian local
ring at their generic points form a locally finite family on a locally Noetherian
integral algebraic space. -/
theorem locallyFinite_primeDivisors_not_mem_henselianLocalRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (f : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      {x | ¬ Z.mem_henselianLocalRing (f : RationalFunction X) ∧ x ∈ Z.pointsSet} :=
  sorry

/-- The prime divisors along which a rational unit has nonzero order form a locally
finite family on a locally Noetherian integral algebraic space. -/
theorem locallyFinite_primeDivisors_ord_ne_zero {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (f : (RationalFunction X)ˣ) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if Z.ord f = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
