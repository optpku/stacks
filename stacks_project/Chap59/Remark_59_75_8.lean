/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.DirectImage
import ReasLib.AlgebraicGeometry.Scheme.Henselization.Fiber
import StacksCheckRecall

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Remark 59.75.8 (1): specialization commutes with the canonical comparison from
stalks of derived direct images to strict-henselian base-change cohomology, for every
scheme morphism and every unbounded étale complex. -/
@[stacks 0GJ9] #check
  (AlgebraicGeometry.Scheme.Etale.derivedPushforward_specialization_leftSquare :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s t : GeometricPoint S)
      (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
      (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
      (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
    CommSq (Cohomology.etaleStalkToStrictHenselizationCohomology f s K)
      (derivedPushforward_specializationMap f s t point point_over K)
      (strictHenselizationCohomologyPullback f s t point point_over K)
      (Cohomology.etaleStalkToStrictHenselizationCohomology f t K))

/- Remark 59.75.8 (2): a morphism completing the geometric-fiber cohomology square
need not exist, even for quasi-compact quasi-separated morphisms and bounded-below
étale complexes. -/
@[stacks 0GJ9] #check
  (AlgebraicGeometry.Scheme.Etale.not_forall_exists_fiberSpecialization :
    ¬ ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (s t : GeometricPoint S)
      (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
      (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
      (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})),
      ∃ φ, CommSq (Cohomology.strictHenselizationToGeometricFiberCohomology f s K.obj)
        (strictHenselizationCohomologyPullback f s t point point_over K.obj) φ
        (Cohomology.strictHenselizationToGeometricFiberCohomology f t K.obj))
