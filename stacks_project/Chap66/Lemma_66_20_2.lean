/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SectionVanishing
import StacksCheckRecall

/-!
# Largest vanishing open of a local section on `X_spaces,étale`

The vanishing locus is realized by an open subspace. The restriction and geometric-germ
characterizations describe the largest such open and all three conclusions of the lemma.
-/

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.20.2 (1): the vanishing locus is the largest open on which the section is zero. -/
@[stacks 04K9] #check
  (AlgebraicGeometry.AlgebraicSpace.sectionRestrict_eq_zero_iff_pointsSet_subset :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
      (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (W : OpenSubspace U.left),
      sectionRestrict F (openSubspaceHom U W) σ = 0 ↔
        W.pointsSet ⊆ sectionVanishingSet F U σ)

/- The vanishing locus is the point set of an actual open subspace. -/
#check (AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_sectionVanishingSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)),
    ∃ W : OpenSubspace U.left, W.pointsSet = sectionVanishingSet F U σ)

/- Conclusion (2): restriction along every site arrow vanishes precisely over this open. -/
#check (AlgebraicGeometry.AlgebraicSpace.sectionRestrict_eq_zero_iff_range_subset :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) {V : spacesEtaleSite X} (φ : V ⟶ U),
    sectionRestrict F φ σ = 0 ↔
      Set.range (Points.map φ.left) ⊆ sectionVanishingSet F U σ)

/- Conclusion (3): the germ at the composed geometric point vanishes precisely on this open. -/
#check (AlgebraicGeometry.AlgebraicSpace.sectionGerm_eq_zero_iff_mem :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})
    (U : spacesEtaleSite X) (σ : F.obj.obj (op U)) (ubar : GeometricPoint U.left),
    sectionGerm F U σ ubar = sectionGerm_zero F U ubar ↔
      ubar.image ∈ sectionVanishingSet F U σ)

end AlgebraicGeometry.AlgebraicSpace
