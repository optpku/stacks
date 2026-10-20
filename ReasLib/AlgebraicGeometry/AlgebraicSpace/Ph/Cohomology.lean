/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Adjunction

/-!
# Ph and étale cohomology of algebraic spaces

Étale cohomology with torsion coefficients agrees with ph cohomology of the
canonical inverse image, both for sheaves and for bounded-below complexes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

/-- Étale cohomology of a locally torsion abelian sheaf on an algebraic space
is isomorphic to ph cohomology of its inverse image. -/
theorem cohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (q : ℕ) :
    IsIsomorphic (etaleCohomology X F q)
      (((siteAbelianSectionsFunctor (bigPhSite X)
          (Over.mk (𝟙 X))).rightDerived q).obj ((aInverseImage X).obj F)) :=
  sorry

/-- Étale hypercohomology of a bounded-below complex with torsion cohomology
sheaves on an algebraic space is isomorphic to ph hypercohomology of its inverse image. -/
theorem plusCohomology_aInverseImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion (smallEtaleTopology X)) K)
    (q : ℤ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((Cochain.functor (globalSections X)).obj (DerivedCategory.Plus.ι.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((RΓ[bigPhSite X](Over.mk (𝟙 X))).obj
          (DerivedCategory.Plus.ι.obj ((plusAInverseImage X).obj K)))) :=
  sorry

/-- Étale and ph cohomology of an algebraic space with constant coefficients
in a torsion abelian group are isomorphic. -/
theorem cohomology_constant {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) (hA : AddMonoid.IsTorsion A) (q : ℕ) :
    IsIsomorphic
      (etaleCohomology X
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) q)
      (((siteAbelianSectionsFunctor (bigPhSite X) (Over.mk (𝟙 X))).rightDerived q).obj
        ((constantSheaf (bigPhSite X) AddCommGrpCat.{u + 1}).obj A)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
