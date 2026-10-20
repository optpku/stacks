/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Forget
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact.Degree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive bounded derived sections

This file specializes the exact-second-functor API to sections of module sheaves on an open
subset.  It canonically compares module-valued bounded derived sections, after forgetting the
section-ring action, with the bounded right-derived functor of additive sections.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections

variable {X : RingedSpace.{u}}

/-- The canonical bounded right-derived cohomology functor of additive sections on `U`. -/
@[stacks 0D6J "bounded additive cohomology on an open"]
abbrev boundedAbCohomologyFunctor
    (X : RingedSpace.{u}) (U : Opens X.carrier) (p : ℤ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  Functor.RightDerived.Bounded.degree (moduleSectionsAsAbelianFunctor X U) p

/-- Bounded-below derived module-valued sections, restricted to sheaves in degree zero. -/
@[stacks 0D6J "bounded module-valued derived sections target"]
abbrev boundedTarget (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ DerivedCategory.Plus (ModuleCat (sectionsRingOnOpen X U)) :=
  DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
    Functor.RightDerived.Bounded.functor (moduleSectionsEvaluationFunctor X U)

/-- Bounded derived additive sections, included in the unbounded additive derived category. -/
@[stacks 0D6J "bounded additive derived sections target"]
abbrev boundedAbTarget (X : RingedSpace.{u}) (U : Opens X.carrier) :
    X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
    Functor.RightDerived.Bounded.functor (moduleSectionsAsAbelianFunctor X U) ⋙
    DerivedCategory.Plus.ι

/-- Module-valued bounded derived sections followed by the exact derived forgetful functor are
canonically the bounded derived functor of additive sections. -/
@[stacks 0D6J "bounded derived sections underlying comparison"]
noncomputable def boundedDerivedForgetIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.RightDerived.Bounded.functor (moduleSectionsEvaluationFunctor X U) ⋙
        ExactFunctor.Derived.Plus.functor (exactForget X U) ≅
      Functor.RightDerived.Bounded.functor (moduleSectionsAsAbelianFunctor X U) :=
  Functor.RightDerived.Composition.BoundedBelow.ExactSecond.iso
    (moduleSectionsEvaluationFunctor X U) (exactForget X U)

/-- In every integral degree, forgetting the section-module structure on bounded derived
cohomology canonically recovers the bounded right-derived degree of additive sections. -/
@[stacks 0D6J "bounded derived cohomology underlying comparison"]
noncomputable def boundedCohomologyForgetIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) (p : ℤ) :
    Functor.RightDerived.Bounded.degree (moduleSectionsEvaluationFunctor X U) p ⋙
        forgetFunctor X U ≅
      boundedAbCohomologyFunctor X U p :=
  Functor.RightDerived.Composition.BoundedBelow.ExactSecond.degreeIso
    (moduleSectionsEvaluationFunctor X U) (exactForget X U) p

/-- The comparison between the two derived additive targets at one module sheaf. -/
@[stacks 0D6J "bounded derived sections underlying comparison object"]
noncomputable def boundedTargetForgetAppIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) (F : X.Modules) :
    ((boundedTarget X U ⋙ underlyingDerivedFunctor X U).obj F) ≅
      (boundedAbTarget X U).obj F :=
  (exactDerivedForgetCompιIso X U).symm.app
      ((Functor.RightDerived.Bounded.functor
        (moduleSectionsEvaluationFunctor X U)).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F)) ≪≫
    (DerivedCategory.Plus.ι :
      DerivedCategory.Plus AddCommGrpCat.{u} ⥤
        DerivedCategory AddCommGrpCat.{u}).mapIso
      ((boundedDerivedForgetIso X U).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj F))

/-- The objectwise bounded-target forgetful comparisons are natural in the module sheaf. -/
@[stacks 0D6J "naturality of bounded derived sections underlying comparison"]
theorem boundedTargetForgetAppIso_hom_naturality
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    {F G : X.Modules} (f : F ⟶ G) :
    (boundedTarget X U ⋙ underlyingDerivedFunctor X U).map f ≫
        (boundedTargetForgetAppIso X U G).hom =
      (boundedTargetForgetAppIso X U F).hom ≫ (boundedAbTarget X U).map f := sorry

/-- Forgetting the module structure on the bounded derived-sections target canonically gives the
bounded additive target in the common unbounded derived category. -/
@[stacks 0D6J "bounded derived sections underlying target comparison"]
noncomputable def boundedTargetForgetIso
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    boundedTarget X U ⋙ underlyingDerivedFunctor X U ≅ boundedAbTarget X U :=
  NatIso.ofComponents (boundedTargetForgetAppIso X U)
    (fun f ↦ boundedTargetForgetAppIso_hom_naturality X U f)

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections
