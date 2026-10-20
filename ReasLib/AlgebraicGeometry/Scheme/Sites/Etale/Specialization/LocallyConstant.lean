/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Stalk

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- Every geometric lift into a pointed strict henselization induces a bijective
specialization map on the stalks of the supplied étale sheaf of sets. -/
def étaleSpecializationMapsBijective {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u)) : Prop :=
  ∀ (sbar tbar : GeometricPoint S)
    (point : Spec (.of tbar.K) ⟶ strictHenselizationAt S sbar)
    (point_over : point ≫ StrictHenselization.toScheme S sbar = tbar.hom),
    Function.Bijective
      (((StrictHenselianNeighborhood.canonical sbar).specializationPoint
        point point_over).sheafFiber.app F)

/-- Specialization maps of a finite locally constant étale sheaf of sets are bijective. -/
theorem IsFiniteLocallyConstant.bijective_étaleSpecializationMap {S : Scheme.{u}}
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    {F : Sheaf S.smallEtaleTopology (Type u)}
    (hF : CategoryTheory.Sheaf.IsFiniteLocallyConstant F) :
    étaleSpecializationMapsBijective F := sorry

/-- Finite geometric stalks together with bijective specialization maps imply finite
local constancy, when every quasi-compact open of the scheme has finitely many
irreducible components. -/
theorem isFiniteLocallyConstant_of_finiteStalks_bijectiveSpecialization
    {S : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u))
    (hFinite : ∀ sbar : GeometricPoint S, Finite (Scheme.Etale.stalk sbar F.obj))
    (hSp : étaleSpecializationMapsBijective F) :
    CategoryTheory.Sheaf.IsFiniteLocallyConstant F := sorry

/-- On a scheme whose quasi-compact opens have finitely many irreducible components,
an étale sheaf of sets is finite locally constant if and only if every geometric
stalk is finite and every canonical specialization map is bijective. -/
theorem finiteLocallyConstant_iff_finiteStalks_bijectiveSpecialization
    {S : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens S]
    [HasWeakSheafify S.smallEtaleTopology (Type u)]
    [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
    (F : Sheaf S.smallEtaleTopology (Type u)) :
    CategoryTheory.Sheaf.IsFiniteLocallyConstant F ↔
      (∀ sbar : GeometricPoint S, Finite (Scheme.Etale.stalk sbar F.obj)) ∧
        étaleSpecializationMapsBijective F := sorry

end AlgebraicGeometry.Scheme
