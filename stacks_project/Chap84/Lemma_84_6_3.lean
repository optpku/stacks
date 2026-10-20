/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

/- Lemma 84.6.3
Étale cohomology agrees with fppf cohomology after the canonical inverse image.
-/
@[stacks 0DGH] #check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.cohomology_aInverseImage :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIsomorphic (etaleCohomology X F q)
      (((siteAbelianSectionsFunctor ((fppfTopology S).over X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseAb X).obj F)))

@[stacks 0DGH] #check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.plusCohomology_aInverseImage :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (q : ℤ),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Cochain.functor (globalSections X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[(fppfTopology S).over X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((aInverseAbPlus X).obj K)))))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverseAb_obj_constantSheaf :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}),
    IsIsomorphic
      ((aInverseAb X).obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}).obj A))

@[stacks 0DGH] #check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.cohomology_constant :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIsomorphic
      (etaleCohomology X
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) q)
      (((siteAbelianSectionsFunctor ((fppfTopology S).over X)
          (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf ((fppfTopology S).over X) AddCommGrpCat.{u + 1}).obj A)))

end

end
