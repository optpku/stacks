/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles.StalkCompatibility
public import stacks_project.Chap59.Lemma_59_94_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.EtaleVanishingCycles

universe u

/- Lemma 59.94.2: for quasi-compact quasi-separated `f` and bounded-below coefficients
relative to which `f` is locally acyclic, geometric stalk specialization and geometric-fibre
cospecialization commute with the two base-change maps. -/
@[stacks 0GJV] #check (AlgebraicGeometry.Scheme.etaleCohomologyCospecialization_commSq :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (s t : GeometricPoint S) (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
    (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
    (K : DerivedCategory.Plus (Coefficients X)) [LocallyAcyclicRelative f K.obj],
    Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f s K.obj =
      Etale.derivedPushforward_specializationMap f s t point point_over K.obj ≫
        Etale.Cohomology.etaleStalkToGeometricFiberBaseChange f t K.obj ≫
          Etale.Cohomology.cospecialization f s t point point_over K)
