/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import ReasLib.Algebra.Module.Devissage.FinitePresentation
public import ReasLib.RingTheory.Flatness.FiberBasis.AtPrime
public import ReasLib.RingTheory.Flat.Projective.GeometricallyIntegral

/-!
# Decomposition from a complete module dévissage

This file records the decomposition obtained after a principal localization from a complete
module dévissage.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped DirectSum

universe u

namespace Module.Devissage.Complete

variable {R : Type u} [CommRing R]
variable {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
variable {N : FGModuleCat.{u} S.obj} [Module R N] [IsScalarTower R S.obj N]
  [Module.FinitePresentation S.obj N] [Module.Flat R N]
variable {r : PrimeSpectrum R}

/-- After one principal localization away from the given prime, a finitely presented module
flat over the base and equipped with a complete dévissage decomposes into the localized stage
algebras with their dévissage multiplicities. Each localized stage algebra is smooth with
geometrically irreducible fibres, and the localized module is projective over the localized
base. -/
theorem existsAwayDecomposition (D : Complete R S N r) :
    ∃ f : R, f ∉ r.asIdeal ∧
      Nonempty
        (LocalizedModule.Away f N ≃ₗ[R]
          ⨁ i : Fin (D.last + 1),
            (Fin (D.stage i).rank →
              Localization.Away (algebraMap R (D.stage i).B f))) ∧
      (∀ i : Fin (D.last + 1),
        (Localization.awayMap (algebraMap R (D.stage i).B) f).Smooth ∧
          GeometricallyIrreducible
            (Spec.map
              (ofHom (Localization.awayMap (algebraMap R (D.stage i).B) f)))) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f N) := sorry

end Module.Devissage.Complete
