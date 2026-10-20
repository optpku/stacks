/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ProperStalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

universe u

/- Lemma 59.91.13. For a proper morphism, the geometric stalks of higher direct images
of a torsion abelian étale sheaf are canonically its geometric-fibre cohomology groups;
for a bounded-below derived object with torsion cohomology, the same holds degreewise. -/
@[stacks 0DDF] #check
  (AlgebraicGeometry.Scheme.Hom.higherDirectImage_stalk_eq_geometricFiberCohomology :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y) [IsProper f]
      (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : IsLocallyTorsion F) (n : ℕ),
      IsIso (AlgebraicGeometry.Scheme.Hom.higherDirectImageStalkToGeometricFiberCohomology
        f ybar F n))

#check
  (AlgebraicGeometry.Scheme.Hom.derivedHigherDirectImage_stalk_eq_geometricFiberCohomology :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (ybar : GeometricPoint Y) [IsProper f]
      (E : (DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})))
      (hE : DerivedCategory.Plus.cohomologyIn
        (IsLocallyTorsion :
          ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E)
      (n : ℤ),
      IsIso (AlgebraicGeometry.Scheme.Hom.derivedHigherDirectImageStalkToGeometricFiberCohomology
        f ybar ((DerivedCategory.Plus.ι).obj E) n))
