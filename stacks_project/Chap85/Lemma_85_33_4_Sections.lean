/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSections

/-! # Compatibility checks for derived étale global sections -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable (U : SimplicialObject (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.hasTerminal_spacesEtaleSite X :
    HasTerminal (spacesEtaleSite X))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.hasGlobalSectionsFunctor_spacesEtaleTotalTopology U :
    HasGlobalSectionsFunctor (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.hasGlobalSectionsFunctor_spacesEtaleTotalTopology_types U :
    HasGlobalSectionsFunctor (spacesEtaleTotalTopology U) (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSections_hasRightDerivedFunctor X :
    (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSectionsTotal_hasRightDerivedFunctor U :
    (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSections X :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSections_eq X :
    plusGlobalSections X =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.globalSectionsIsoSectionsSelf X :
    Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≅
      (sheafSections (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (op (spacesEtaleSite.self X)))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSectionsTotal U :
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSectionsTotal_eq U :
    plusGlobalSectionsTotal U =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
