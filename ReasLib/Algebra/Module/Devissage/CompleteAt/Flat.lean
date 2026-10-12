/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.Algebra.Module.Devissage.CompleteAt
public import ReasLib.Algebra.Module.Devissage.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.Exact
public import ReasLib.Algebra.Module.Projective.LocalRing
public import ReasLib.RingTheory.Flatness.FiberBasis

@[expose] public section

open scoped DirectSum

universe u

namespace Module.Devissage.CompleteAt

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
variable {N : Type u} [AddCommGroup N] [Module S.obj N] [Module R N]
  [IsScalarTower R S.obj N] [Module.Finite S.obj N]
variable {q : PrimeSpectrum S.obj}
variable {hq : (IsLocalRing.closedPoint R).asIdeal =
  q.asIdeal.comap (algebraMap R S.obj)}

/-- A finite module with a complete dévissage at a prime and flat localization there is
finitely presented over its algebra. -/
theorem finitePresentation_of_flatAt
    (D : CompleteAt R S (FGModuleCat.of S.obj N) (IsLocalRing.closedPoint R) q hq)
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)) :
    Module.FinitePresentation S.obj N := sorry

/-- A finite module with a complete dévissage at a prime and flat localization there is
noncanonically linearly equivalent over the base ring to the direct sum of its stage algebras,
with multiplicities given by the stage ranks. -/
theorem nonempty_linearEquiv_directSum_of_flatAt
    (D : CompleteAt R S (FGModuleCat.of S.obj N) (IsLocalRing.closedPoint R) q hq)
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)) :
    Nonempty
      (N ≃ₗ[R]
        ⨁ i : Fin (D.toComplete.last + 1),
          (Fin (D.toComplete.stage i).rank → (D.toComplete.stage i).B)) := sorry

/-- A finite module with a complete dévissage at a prime and flat localization there is free
over the local base ring. -/
theorem free_of_flatAt
    (D : CompleteAt R S (FGModuleCat.of S.obj N) (IsLocalRing.closedPoint R) q hq)
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal N)) :
    Module.Free R N := sorry

end Module.Devissage.CompleteAt
