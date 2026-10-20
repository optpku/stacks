module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.LocallyConstant.Module
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

/- Lemma 59.75.6: on a scheme whose quasi-compact opens have finitely many
irreducible components (for example if the underlying space is Noetherian, or if
the scheme is locally Noetherian), and for a Noetherian ring `Λ`, a sheaf of
`Λ`-modules on the small étale site is finite type and locally constant if and
only if every geometric stalk is a finite `Λ`-module and every specialization
map `sp : F_s̄ → F_t̄` is bijective. -/
@[stacks 0GKC] #check
  (AlgebraicGeometry.Scheme.finiteTypeLocallyConstantModule_iff_finiteStalks_bijectiveSpecialization :
    ∀ {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens S]
      [IsNoetherianRing Λ]
      [HasWeakSheafify S.smallEtaleTopology (Type u)]
      [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
      [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
      [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
      [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
      (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)),
      CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F ↔
        (∀ sbar : Scheme.GeometricPoint S, Module.Finite Λ (Scheme.étaleModuleStalk sbar F)) ∧
          Scheme.étaleSpecializationMapsBijective_module F)
