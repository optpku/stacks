/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal

@[expose] public section

open AlgebraicGeometry Order

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicCycle.locallyFiniteSupport_ord :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (f : X.functionFieldˣ),
    LocallyFiniteSupport (fun x : X ↦ X.ord f x))

#check (AlgebraicGeometry.AlgebraicCycle.principal :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X],
    X.functionFieldˣ → AlgebraicCycle X ℤ)

#check (AlgebraicGeometry.AlgebraicCycle.principal_apply :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (x : X),
    AlgebraicGeometry.AlgebraicCycle.principal X f x = X.ord f x)

#check (AlgebraicGeometry.AlgebraicCycle.principal_apply_eq_zero_of_coheight_ne_one :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (x : X),
    coheight x ≠ 1 → AlgebraicGeometry.AlgebraicCycle.principal X f x = 0)

#check (AlgebraicGeometry.AlgebraicCycle.principal_apply_primeDivisor :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X),
    AlgebraicGeometry.AlgebraicCycle.principal X f Z.genericPoint =
      (X.principalWeilDivisor f).coeff Z)
