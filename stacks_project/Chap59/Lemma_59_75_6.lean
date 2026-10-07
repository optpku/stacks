module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Lemma_59_75_5
public import stacks_project.Chap59.Lemma_59_75_6_Stalk

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme.Etale.Small

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- All specialization maps of an étale sheaf of `Λ`-modules, after forgetting
to sets and applying the identifications of Remark 59.75.2, are bijective. -/
def étaleSpecializationMapsBijective_module
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  étaleSpecializationMapsBijective
    ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u} Λ))).obj F)

/-- Geometric stalks of a finite-type locally constant étale sheaf of
`Λ`-modules are finite `Λ`-modules. -/
theorem IsFiniteTypeLocallyConstantModule.finite_etaleModuleStalk
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [IsNoetherianRing Λ]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    {F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (hF : CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F)
    (sbar : GeometricPoint S) :
    Module.Finite Λ (étaleModuleStalk sbar F) := sorry

/-- Specialization maps of a finite-type locally constant étale sheaf of
`Λ`-modules are bijective. -/
theorem IsFiniteTypeLocallyConstantModule.bijective_étaleSpecializationMap
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [IsNoetherianRing Λ]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    {F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (hF : CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F) :
    étaleSpecializationMapsBijective_module F := sorry

/-- Finite geometric `Λ`-module stalks together with bijective specialization
maps imply finite-type local constancy, when every quasi-compact open of `S`
has finitely many irreducible components and `Λ` is Noetherian. -/
theorem IsFiniteTypeLocallyConstantModule.of_finiteStalks_bijectiveSpecialization
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [IsNoetherianRing Λ]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    (hFinite : ∀ sbar : GeometricPoint S, Module.Finite Λ (étaleModuleStalk sbar F))
    (hSp : étaleSpecializationMapsBijective_module F) :
    CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F := sorry

/-- Lemma 59.75.6: on a scheme whose quasi-compact opens have finitely many
irreducible components (for example if the underlying space is Noetherian, or if
the scheme is locally Noetherian), and for a Noetherian ring `Λ`, a sheaf of
`Λ`-modules on the small étale site is finite type and locally constant if and
only if every geometric stalk is a finite `Λ`-module and every specialization
map `sp : F_s̄ → F_t̄` is bijective. -/
@[stacks 0GKC]
theorem finiteTypeLocallyConstantModule_iff_finiteStalks_bijectiveSpecialization
    [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [IsNoetherianRing Λ]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [HasWeakSheafify S.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) :
    CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule F ↔
      (∀ sbar : GeometricPoint S, Module.Finite Λ (étaleModuleStalk sbar F)) ∧
        étaleSpecializationMapsBijective_module F := sorry

end AlgebraicGeometry.Scheme
