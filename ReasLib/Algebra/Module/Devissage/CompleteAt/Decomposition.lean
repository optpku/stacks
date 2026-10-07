module

public import ReasLib.Algebra.Module.Devissage.Complete.Decomposition
public import ReasLib.Algebra.Module.Devissage.CompleteAt.Flat
public import ReasLib.RingTheory.Flat.Locus

/-!
# Decomposition from a complete module dévissage at a prime

This file records the decomposition obtained after a principal localization from a complete
module dévissage at a prime where the module is flat over the base.
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped DirectSum

universe u

namespace Module.Devissage.CompleteAt

variable {R : Type u} [CommRing R]
variable {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
variable {N : FGModuleCat.{u} S.obj} [Module R N] [IsScalarTower R S.obj N]
  [Module.FinitePresentation S.obj N]
variable {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
variable {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}

/-- After one principal localization away from the base prime, a finitely presented module
equipped with a complete dévissage at a prime in its flatness locus decomposes into the localized
stage algebras with their dévissage multiplicities. Each localized stage algebra is smooth with
geometrically irreducible fibres, and the localized module is projective over the localized base. -/
theorem existsAwayDecomposition
    (D : CompleteAt R S N r q hq) (hflat : q ∈ Module.flatOverBaseLocus R S.obj N) :
    ∃ f : R, f ∉ r.asIdeal ∧
      Nonempty
        (LocalizedModule.Away f N ≃ₗ[R]
          ⨁ i : Fin (D.toComplete.last + 1),
            (Fin (D.toComplete.stage i).rank →
              Localization.Away (algebraMap R (D.toComplete.stage i).B f))) ∧
      (∀ i : Fin (D.toComplete.last + 1),
        (Localization.awayMap (algebraMap R (D.toComplete.stage i).B) f).Smooth ∧
          GeometricallyIrreducible
            (Spec.map
              (ofHom (Localization.awayMap (algebraMap R (D.toComplete.stage i).B) f)))) ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f N) := sorry

end Module.Devissage.CompleteAt
