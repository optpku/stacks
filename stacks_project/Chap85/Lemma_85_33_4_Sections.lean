module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.GlobalSections.Additive
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap85.Lemma_85_33_1_Etale

/-!
# Bounded-below derived global sections on spaces-étale sites

Global sections of abelian sheaves on `X_étale` are `Sheaf.Γ` for
`spacesEtaleTopology X`, using that `spacesEtaleSite.self X` is terminal.
The total spaces-étale site of a simplicial algebraic space has the same
topos-level owner. Bounded-below derived functors of these global-sections
functors are `RΓ(X_étale, -)` and `RΓ(U_étale, -)` on `D⁺`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- The identity object `spacesEtaleSite.self X` is a terminal object of the
spaces-étale site, so that site has a terminal object. -/
instance hasTerminal_spacesEtaleSite (X : AlgebraicSpace S) :
    HasTerminal (spacesEtaleSite X) :=
  IsTerminal.hasTerminal (isTerminal_self X)

/-- The total spaces-étale site of a simplicial algebraic space admits a global
sections functor on abelian sheaves. -/
instance hasGlobalSectionsFunctor_spacesEtaleTotalTopology
    (U : SimplicialObject (AlgebraicSpace S)) :
    HasGlobalSectionsFunctor (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  sorry

/-- The bounded-below right-derived functor of global sections on `X_étale` exists. -/
instance plusGlobalSections_hasRightDerivedFunctor (X : AlgebraicSpace S) :
    (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) :=
  sorry

/-- The bounded-below right-derived functor of global sections on `U_étale` exists. -/
instance plusGlobalSectionsTotal_hasRightDerivedFunctor
    (U : SimplicialObject (AlgebraicSpace S)) :
    (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Bounded-below derived global sections `RΓ(X_étale, -)` on `D⁺`. -/
def plusGlobalSections (X : AlgebraicSpace S) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  Functor.RightDerived.Bounded.functor
    (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1})

/-- `plusGlobalSections X` is the canonical bounded-below right-derived functor of
`Sheaf.Γ` on `spacesEtaleTopology X`. -/
theorem plusGlobalSections_eq (X : AlgebraicSpace S) :
    plusGlobalSections X =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  sorry

/-- On `X_étale`, global sections are evaluation at the terminal object
`spacesEtaleSite.self X`. -/
def globalSectionsIsoSectionsSelf (X : AlgebraicSpace S) :
    Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≅
      (sheafSections (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (op (spacesEtaleSite.self X)) :=
  Sheaf.ΓNatIsoSheafSections (spacesEtaleTopology X) AddCommGrpCat.{u + 1}
    (isTerminal_self X)

/-- Bounded-below derived global sections `RΓ(U_étale, -)` on `D⁺` of the total
spaces-étale site. -/
def plusGlobalSectionsTotal (U : SimplicialObject (AlgebraicSpace S)) :
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  Functor.RightDerived.Bounded.functor
    (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

/-- `plusGlobalSectionsTotal U` is the canonical bounded-below right-derived functor of
`Sheaf.Γ` on `spacesEtaleTotalTopology U`. -/
theorem plusGlobalSectionsTotal_eq (U : SimplicialObject (AlgebraicSpace S)) :
    plusGlobalSectionsTotal U =
      Functor.RightDerived.Bounded.functor
        (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
