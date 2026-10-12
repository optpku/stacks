/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Surface

open AlgebraicGeometry CategoryTheory

universe u

section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
variable (S : AlgebraicGeometry.SurfaceModification A)

/- Situation 54.7.1 (1): `A` is local. -/
@[stacks 0AX8] #check (AlgebraicGeometry.SurfaceModification.localRing A S : IsLocalRing A)

/- Situation 54.7.1 (2): `A` is Noetherian. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.noetherianRing A S : IsNoetherianRing A)

/- Situation 54.7.1 (3): `A` is normal. -/
@[stacks 0AX8] #check (AlgebraicGeometry.SurfaceModification.normalRing A S : IsNormalRing A)

/- Situation 54.7.1 (4): `A` is a domain. -/
@[stacks 0AX8] #check (AlgebraicGeometry.SurfaceModification.domain A S : IsDomain A)

/- Situation 54.7.1 (5): `A` has Krull dimension `2`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.dimension A S : ringKrullDim A = 2)

/- Situation 54.7.1 (6): `𝔪` is the maximal ideal of `A`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.maximalIdeal A S : Ideal A)

/- Situation 54.7.1 (7): `κ` is the residue field of `A`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.residueField A S : Type u)

/- Situation 54.7.1 (8): `S` is `Spec A`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.base A S : Scheme.{u})

/- Situation 54.7.1 (9): `s` is the closed point of `S = Spec A`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.closedPoint A S : PrimeSpectrum A)

/- Situation 54.7.1 (10): `U` is the punctured spectrum `S \ {s}`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.puncturedSpectrum A S : Scheme.{u})

/- Situation 54.7.1 (11): `f : X ⟶ S` is a modification. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.isModification A S : IsModification S.f)

/- Situation 54.7.1 (12): `C₁, …, Cᵣ` enumerate the irreducible components of the special
fibre `X_s`. -/
@[stacks 0AX8] #check
  (AlgebraicGeometry.SurfaceModification.components A S :
    Fin S.r ≃ irreducibleComponents (S.f.fiber (IsLocalRing.closedPoint A)))

end
