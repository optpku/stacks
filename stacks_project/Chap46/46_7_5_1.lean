/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison.Plus
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Property
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.BoundedComparison
public import stacks_project.Chap46.Lemma_46_7_4_Instances
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

variable (τ : StandardTopology) (A : CommRingCat.{u})
variable [Abelian (RingedSite.ModuleCat.{u}
  (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
variable [ObjectProperty.IsWeakSerreClass
  (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ)]
variable [HasDerivedCategory.{u} (RingedSite.ModuleCat.{u}
  (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).FullSubcategory]

/- 46.7.5.1: For `U = Spec A`, the inclusion of adequate module sheaves on the big `τ`-site
induces the canonical functor from their bounded-below derived category to the bounded-below
ambient derived subcategory whose cohomology sheaves are adequate. -/
@[stacks 06VV] #check
  (CategoryTheory.DerivedCategory.Plus.CohomologyIn.Comparison.functor
    (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ) :
      DerivedCategory.Plus
          (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ).FullSubcategory ⥤
        DerivedCategory.Plus.CohomologyIn
          (SheafOfModules.Adeq.property (Scheme.Spec.obj (op A)) τ))
