module

public import ReasLib.Algebra.Module.Devissage.Complete.Decomposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped DirectSum

universe u

/- Lemma 38.12.2: after one principal localization away from `r`, a finitely presented
`S`-module flat over `R` and equipped with a complete dévissage decomposes, as an
`R`-module, into the localized stage algebras with their dévissage multiplicities.
Each localized stage algebra is smooth over `Localization.Away f` with geometrically
irreducible fibres, and the localized module is projective over `Localization.Away f`. -/
@[stacks 05IB] #check
  (Module.Devissage.Complete.existsAwayDecomposition :
    ∀ {R : Type u} [CommRing R]
      {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
      {N : FGModuleCat.{u} S.obj} [Module R N] [IsScalarTower R S.obj N]
        [Module.FinitePresentation S.obj N] [Module.Flat R N]
      {r : PrimeSpectrum R} (D : Module.Devissage.Complete R S N r),
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
        Module.Projective (Localization.Away f) (LocalizedModule.Away f N))
