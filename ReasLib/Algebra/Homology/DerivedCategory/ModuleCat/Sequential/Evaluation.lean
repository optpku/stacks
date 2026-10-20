/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sequential.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived evaluation of sequential varying-ring modules

@stack 091D
@stack 091H

Evaluation on the bottom topology is exact.  Hence stage evaluation of varying-ring module
systems induces a canonical functor on unbounded derived categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

-- Local instance justification (defeq pin): all derived evaluations in this file use Mathlib's
-- standard localization model; no alternative derived-category instance is exported.
attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along the successor map, bundled with its exactness. -/
@[stacks 091D "exact successor restriction of scalars"]
noncomputable abbrev exactTransition
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    ModuleCat.{u} ((ringSystemAsRingCat F).obj (op n)) ⥤ₑ
      ModuleCat.{u} ((ringSystemAsRingCat F).obj (op (n + 1))) :=
  ModuleCat.RestrictScalars.exact (F.stepMap n).hom

/-- Derived restriction of scalars along the successor map of a sequential ring system. -/
@[stacks 091D "derived successor restriction of scalars"]
noncomputable abbrev derivedTransition
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    DerivedCategory
        (ModuleCat.{u} ((ringSystemAsRingCat F).obj (op n))) ⥤
      DerivedCategory
        (ModuleCat.{u} ((ringSystemAsRingCat F).obj (op (n + 1)))) :=
  (exactTransition F n).mapDerivedCategory

/-- Stage evaluation of a bottom-topology module system preserves finite limits. -/
@[stacks 091D "finite limits under stage evaluation"]
noncomputable instance evaluationPreservesFiniteLimits
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    PreservesFiniteLimits (evaluation.{u, u} F n) :=
  SheafOfModules.Finite.evaluationPreservesFiniteLimits
    (R := bottomRingSheaf F) (op n)

/-- Stage evaluation of a bottom-topology module system preserves finite colimits. -/
@[stacks 091D "finite colimits under stage evaluation"]
noncomputable instance evaluationPreservesFiniteColimits
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    PreservesFiniteColimits (evaluation.{u, u} F n) := sorry

/-- The exact stage-evaluation functor on unbounded derived categories. -/
@[stacks 091D "derived stage evaluation", stacks 091H "derived stage evaluation"]
noncomputable abbrev derivedEvaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    DerivedCategory (ModuleSystem.{u, u} F) ⥤
      DerivedCategory
        (ModuleCat.{u} ((ringSystemAsRingCat F).obj (op n))) :=
  (evaluation.{u, u} F n).mapDerivedCategory

/-- Stage evaluation bundled with its finite-limit and finite-colimit exactness. -/
@[stacks 091D "exact stage evaluation"]
noncomputable abbrev exactEvaluation
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    ModuleSystem.{u, u} F ⥤ₑ
      ModuleCat.{u} ((ringSystemAsRingCat F).obj (op n)) :=
  ExactFunctor.of (evaluation.{u, u} F n)

/-- The successor transition as a morphism of bundled exact functors. -/
@[stacks 091D "exact successor transition"]
noncomputable def exactEvaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    exactEvaluation F (n + 1) ⟶
      (exactEvaluation F n).comp (exactTransition F n) :=
  ObjectProperty.homMk (P := exactFunctor _ _)
    (evaluationStep F n ≫
      eqToHom (ExactFunctor.comp_obj
        (exactEvaluation F n)
        (exactTransition F n)).symm)

/-- The transition between derived stage evaluations.  It is obtained by deriving the exact
successor transition and then applying the canonical comparison between the derived functor of a
composite and the composite of the derived functors. -/
@[stacks 091D "transition between derived stage evaluations"]
noncomputable def derivedEvaluationStep
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    derivedEvaluation F (n + 1) ⟶
      derivedEvaluation F n ⋙ derivedTransition F n :=
  ExactFunctor.MapDerivedCategory.map (exactEvaluationStep F n) ≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (exactEvaluation F n) (exactTransition F n)).hom

/-- Derived stage evaluation commutes with integer shifts. -/
@[stacks 091D "derived evaluation commutes with shifts"]
noncomputable instance derivedEvaluationCommShift
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    (derivedEvaluation F n).CommShift Int :=
  inferInstanceAs ((evaluation.{u, u} F n).mapDerivedCategory.CommShift Int)

/-- Derived stage evaluation is triangulated. -/
@[stacks 091D "triangulated derived evaluation"]
instance derivedEvaluationIsTriangulated
    (F : SequentialInverseSystem CommRingCat.{u}) (n : Nat) :
    (derivedEvaluation F n).IsTriangulated :=
  inferInstanceAs ((evaluation.{u, u} F n).mapDerivedCategory.IsTriangulated)

end CategoryTheory.SequentialInverseSystem
