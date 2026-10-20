/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Vanishing
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived consequences of a topology-comparison situation

The canonical derived functors are defined in `TopologyComparison.Derived`.  This leaf contains
the three source-facing consequences of Lemma 21.30.8 that are useful as reusable propositions.
The bounded-below unit is used throughout; no unbounded derived-adjunction witness is exposed.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology
open DerivedCategory
open scoped CategoryTheory CategoryTheory.GrothendieckTopology DerivedCategory.CohomologyIn

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.Consequences

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

section Unit

variable (hle : τ' ≤ τ)
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    ((comparisonTopologyPushforwardAb hle X).toBoundedBelowDerived)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]

/-- Lemma 21.30.8 (0EZF), unit clause: the bounded-below comparison unit is invertible on
`D⁺[A' X]`. -/
@[stacks 0EZF "(2)"]
theorem unit_isIso_of_cohomologyIn
    (h : Situation τ τ' P A') (hV : Situation.AllVanishing h)
    (X : C) (K' : D⁺[A' X]) :
    IsIso ((GrothendieckTopology.Derived.Plus.unit hle X).app K'.obj) := sorry

end Unit

section Pushforward

variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]

/-- Lemma 21.30.8 (0EZF), direct-image clause: bounded-below direct image preserves the
cohomology-in coefficient property selected by a situation. -/
@[stacks 0EZF "(3)"]
theorem pushforward_mem_cohomologyIn
    (h : Situation τ τ' P A')
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    [∀ Q : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.map f).op.HasPointwiseRightKanExtension Q]
    [Functor.HasRightDerivedFunctor
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (τ'.over X) (τ'.over Y)).toBoundedBelowDerived)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))]
    (K' : D⁺[A' X]) :
    Plus.cohomologyIn (A' Y)
      ((GrothendieckTopology.Derived.Over.Plus.pushforward τ' f).obj K'.obj) := sorry

end Pushforward

section BaseChange

variable (hle : τ' ≤ τ)
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ.over X) (τ.over Y))]

/-- Lemma 21.30.8 (0EZF), base-change clause: inverse image for the finer topology commutes
with bounded-below direct image along a morphism in `P` on `D⁺[A' X]`. -/
@[stacks 0EZF "(4)"]
theorem baseChange_isIso_of_allVanishing
    (h : Situation τ τ' P A')
    (hV : Situation.AllVanishing h)
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    [∀ Q : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
      (Over.map f).op.HasPointwiseRightKanExtension Q]
    [Functor.HasRightDerivedFunctor
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (τ'.over X) (τ'.over Y)).toBoundedBelowDerived)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))]
    [Functor.HasRightDerivedFunctor
      (((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (τ.over X) (τ.over Y)).toBoundedBelowDerived)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (τ.over X) AddCommGrpCat.{max u v}))]
    (K' : D⁺[A' X]) :
    IsIso ((GrothendieckTopology.Derived.Plus.baseChangeOf hle f
      (MorphismProperty.HasPullbacks.hasPullbacksAlong_of_mem h.hasPullbacks hf)).app K'.obj) := sorry

end BaseChange

end CategoryTheory.GrothendieckTopology.TopologyComparison.Consequences

end
