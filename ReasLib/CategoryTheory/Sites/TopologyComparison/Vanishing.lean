/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Situation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local vanishing in a topology-comparison situation

The predicates and coefficient data live in `TopologyComparison.Situation`.  This leaf owns the
degree-induction API, so later comparison arguments can use short names without importing a
chapter file.
-/

open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison.Vanishing

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C,
  ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C,
  HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]

/-- Lemma 21.30.7 (0EZE): the local comparison condition `(V_n)` implies `(V_(n + 1))`. -/
@[stacks 0EZE]
theorem localVanishing_succ
    (h : Situation τ τ' P A') (n : ℕ)
    (hVn : Situation.LocalVanishing h n) :
    Situation.LocalVanishing h (n + 1) := sorry

/-- Lemma 21.30.8 (0EZF), first clause: every local comparison degree satisfies `(V_n)`. -/
@[stacks 0EZF "(1)"]
theorem localVanishing_all
    (h : Situation τ τ' P A') (n : ℕ) :
    Situation.LocalVanishing h n := sorry

/-- The all-degree certificate packages `localVanishing_all` for downstream restriction APIs. -/
@[stacks 0EZF "all-degree local vanishing certificate"]
theorem all
    (h : Situation τ τ' P A') :
    Situation.AllVanishing h := sorry

end CategoryTheory.GrothendieckTopology.TopologyComparison.Vanishing

end
