/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.StalkBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.DerivedProper

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y)

/-- The geometric stalk of derived-direct-image cohomology maps canonically to
cohomology of the derived inverse image on the geometric fibre. -/
def derivedHigherDirectImageStalkToGeometricFiberCohomology
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))) (n : ℤ) :
    (etaleStalkExact ybar).obj.obj
        ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((Etale.Derived.directImage f).obj K)) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        (((siteAbelianSectionsDerived.{u + 1, u, u + 1, u + 1} (pullback f ybar.hom).smallEtaleTopology (globalEtale (pullback f ybar.hom)))).obj
            ((Etale.Derived.inverseImage (pullback.fst f ybar.hom)).obj K)) :=
  (ExactFunctor.homologyIso (etaleStalkExact ybar) ((Etale.Derived.directImage f).obj K) n).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
      (Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f ybar K)

/-- The degreewise geometric-fibre comparison is inverse stalk homology transport
followed by homology of the canonical geometric-fibre base-change map. -/
theorem derivedHigherDirectImageStalkToGeometricFiberCohomology_eq
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))) (n : ℤ) :
    derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar K n =
      (ExactFunctor.homologyIso (etaleStalkExact ybar) ((Etale.Derived.directImage f).obj K) n).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).map
          (Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f ybar K) := rfl

/-- The geometric stalk of a higher direct image maps canonically to the cohomology
of the pulled-back sheaf on the geometric fibre. -/
def higherDirectImageStalkToGeometricFiberCohomology
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    (etaleStalkExact ybar).obj.obj ((Etale.Derived.higherDirectImage f n).obj F) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (((siteAbelianSectionsDerived.{u + 1, u, u + 1, u + 1} (pullback f ybar.hom).smallEtaleTopology (globalEtale (pullback f ybar.hom)))).obj
            ((Etale.Derived.inverseImage (pullback.fst f ybar.hom)).obj
              ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) :=
  derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) (n : ℤ)

/-- The higher-direct-image comparison is the derived comparison applied to the
sheaf placed in degree zero. -/
theorem higherDirectImageStalkToGeometricFiberCohomology_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    higherDirectImageStalkToGeometricFiberCohomology f ybar F n =
      derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar
        ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) (n : ℤ) := rfl

/-- For a proper morphism and a locally torsion abelian étale sheaf, the canonical
comparison from a geometric stalk of each higher direct image to geometric-fibre
cohomology is an isomorphism. -/
theorem higherDirectImage_stalk_eq_geometricFiberCohomology
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) := sorry

/-- The proper geometric-stalk comparison is available to typeclass inference
when the local torsion condition is supplied through `Fact`. -/
instance higherDirectImageStalkToGeometricFiberCohomology_isIso
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [hF : Fact (IsLocallyTorsion F)] (n : ℕ) :
    IsIso (higherDirectImageStalkToGeometricFiberCohomology f ybar F n) :=
  higherDirectImage_stalk_eq_geometricFiberCohomology f ybar F hF.out n

/-- For a proper morphism and a bounded-below derived étale object with locally
torsion cohomology, the canonical comparison from each geometric cohomology stalk
to cohomology on the geometric fibre is an isomorphism. -/
theorem derivedHigherDirectImage_stalk_eq_geometricFiberCohomology
    [IsProper f]
    (E : (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E)
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar
      ((DerivedCategory.Plus.ι).obj E) n) := sorry

/-- The proper derived geometric-stalk comparison is available to typeclass
inference when the torsion-cohomology condition is supplied through `Fact`. -/
instance derivedHigherDirectImageStalkToGeometricFiberCohomology_isIso
    [IsProper f]
    (E : (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})))
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E)]
    (n : ℤ) :
    IsIso (derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar
      ((DerivedCategory.Plus.ι).obj E) n) :=
  derivedHigherDirectImage_stalk_eq_geometricFiberCohomology f ybar E hE.out n

end AlgebraicGeometry.Scheme.Hom

end
