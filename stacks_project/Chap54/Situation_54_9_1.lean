/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RationalSingularity.Situation

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

section

variable (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
variable (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f]
variable (hX : X.isNormal) (r : ℕ)
variable (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))

/- Situation 54.9.1 (1): `A` is a domain. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.domain A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : IsDomain A)

/- Situation 54.9.1 (2): `A` is a two-dimensional normal Nagata local ring defining a
rational singularity. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.rationalSingularity A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : IsRationalSingularity A)

/- Situation 54.9.1 (3): `𝔪` is the maximal ideal of `A`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.maximalIdeal A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : Ideal A)

/- Situation 54.9.1 (4): `κ` is the residue field of `A`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.residueField A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : Type u)

/- Situation 54.9.1 (5): `S` is `Spec A`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.scheme A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : Scheme.{u})

/- Situation 54.9.1 (6): `s` is the closed point of `S = Spec A`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.closedPoint A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : PrimeSpectrum A)

/- Situation 54.9.1 (7): `U` is the punctured spectrum `S \ {s}`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.puncturedSpectrum A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : Scheme.{u})

/- Situation 54.9.1 (8): `f : X ⟶ S` is a modification. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.modification A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : IsModification f)

/- Situation 54.9.1 (9): `X` is normal. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.normal A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) : X.isNormal)

/- Situation 54.9.1 (10): `C₁, …, Cᵣ` enumerate the irreducible components of the special
fibre `X_s`. -/
@[stacks 0B4W] #check
  (AlgebraicGeometry.RationalSingularity.Situation.components A
    (AlgebraicGeometry.RationalSingularity.Situation.of A X f hX r C) :
      Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))

end
