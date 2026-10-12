/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded additive sections and Ext-based sheaf cohomology

The canonical target for additive comparisons is the bounded right-derived degree of additive
sections.  Mathlib's Ext-based `H'` remains available through theorem-level `IsIsomorphic`
companions; this file deliberately does not choose an arbitrary natural isomorphism from those
existence statements.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]

/-- Ext-based cohomology of the underlying additive sheaf, evaluated on an open subset. -/
@[stacks 0D6J "Ext-based underlying cohomology on an open"]
abbrev cohomologyFunctor (U : Opens X.carrier) (p : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  moduleUnderlyingSheaf X ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- Ext-based cohomology of the underlying additive sheaf of a module. -/
@[stacks 0D6J "underlying module cohomology"]
abbrev cohomology (F : X.Modules) (p : ℕ) (U : Opens X.carrier) :
    AddCommGrpCat.{u} :=
  (cohomologyFunctor U p).obj F

/-- Global Ext-based cohomology of the underlying additive sheaf of a module. -/
@[stacks 0D6J "underlying module global cohomology"]
abbrev globalCohomology (F : X.Modules) (p : ℕ) : AddCommGrpCat.{u} :=
  cohomology F p ⊤

/-- The canonical bounded right-derived degree of additive sections represents Ext-based
cohomology of the underlying additive sheaf. -/
@[stacks 0D6J "bounded additive sections compute underlying sheaf cohomology"]
theorem boundedAb_isIsomorphic (U : Opens X.carrier) (p : ℕ) :
    IsIsomorphic
      (boundedAbCohomologyFunctor X U (p : ℤ))
      (cohomologyFunctor U p) := sorry

/-- Forgetting module structure on module-valued bounded cohomology represents Ext-based
cohomology of the underlying additive sheaf. -/
@[stacks 0D6J "forgotten bounded module cohomology computes underlying sheaf cohomology"]
theorem boundedModule_isIsomorphic (U : Opens X.carrier) (p : ℕ) :
    IsIsomorphic
      (Functor.RightDerived.Bounded.degree (moduleSectionsEvaluationFunctor X U) (p : ℤ) ⋙
        forgetFunctor X U)
      (cohomologyFunctor U p) := sorry

end AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Underlying
