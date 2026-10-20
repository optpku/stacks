/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.LocallyConstant
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.RingTheory.Noetherian.Defs

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]

/-- Every canonical specialization map of the underlying sheaf of sets of an étale
module sheaf is bijective. -/
def étaleSpecializationMapsBijective_module
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))]
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  étaleSpecializationMapsBijective
    ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u} Λ))).obj F)

/-- On a scheme whose quasi-compact opens have finitely many irreducible components,
an étale sheaf of modules over a Noetherian ring is finite type and locally constant
if and only if every geometric module stalk is finitely generated and every
specialization map is bijective. -/
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
