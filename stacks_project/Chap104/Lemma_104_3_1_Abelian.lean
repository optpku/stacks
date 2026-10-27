/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedLowerShriek

/-!
# Derived abelian inverse-image compatibility

Inverse-image spellings for the lisse-étale and flat-fppf inclusions, together
with typed checks of their canonical derived lower-shriek adjunctions.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- Derived inverse image of abelian sheaves along the lisse-étale inclusion. -/
abbrev lisseEtaleAbelianInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}]
    [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{z}]
    [HasSheafify X.etaleTopology AddCommGrpCat.{z}] :
    DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
    (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)

/-- Derived inverse image of abelian sheaves along the flat-fppf inclusion. -/
abbrev flatFppfAbelianInverseImageDerived (X : GroupoidsOver S)
    [AlgebraicStack X] [UnivLE.{u + 1, z}]
    [HasSheafify (flatFppfTopology X) AddCommGrpCat.{z}]
    [HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{z}] :
    DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) ⥤
      DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) :=
  siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
    (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)

variable (X : GroupoidsOver S) [AlgebraicStack X] [UnivLE.{u + 1, z}]

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived.adjunction X :
  lisseEtaleAbelianLowerShriekDerived.{u, z} X ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived.adjunction X :
  flatFppfAbelianLowerShriekDerived.{u, z} X ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))

end AlgebraicGeometry.AlgebraicStack
