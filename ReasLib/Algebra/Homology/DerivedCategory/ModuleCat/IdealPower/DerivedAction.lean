/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedAction
public import ReasLib.Algebra.Module.IdealPower.Submodule
public import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-power factorization through the derived action

This leaf owns the reusable derived-category formulation of the eventual ideal-power
factorization.  The target is the two-variable derived tensor bifunctor, followed by the
canonical degree-zero action; no monoidal structure on the derived category is required.

@stack 064M
@stack 0928
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat.DerivedAction

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.Action

variable {A : Type u} [CommRing A]

/-- The derived action of an ideal on a degree-zero module, induced by `I ⟶ A`. -/
@[stacks 064M "ideal action on a degree-zero derived module"]
noncomputable def idealAction (I : Ideal A) (M : ModuleCat A) :
    DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A I)) (ModuleCat.single0 M) ⟶
      ModuleCat.single0 M :=
  (DerivedTensor.Bifunctor.rightFunctor (ModuleCat.single0 M)).map
      (ModuleCat.single0Functor.map (ModuleCat.ofHom I.subtype)) ≫
    derivedAction M

/-- The ideal-power inclusion factors through `I[0] ⊗ᴸ M[0]` for some positive power.

The action map is the canonical `I[0] ⊗ᴸ M[0] ⟶ M[0]` induced by `I ⟶ A`; this is the
library-facing form of Stacks Project, Lemma 15.102.7 (0928). -/
@[stacks 0928 "eventual ideal-power factorization through derived tensor action"]
theorem existsFactorization
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ n : ℕ, 0 < n ∧
      ∃ α : ModuleCat.single0 (Ideal.PowerSubmodule.stageObj I M n) ⟶
          DerivedTensor.Bifunctor.obj (ModuleCat.single0 (ModuleCat.of A I))
            (ModuleCat.single0 M),
        α ≫ idealAction I M =
          ModuleCat.single0Functor.map
            (ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I M n)) := sorry

end CategoryTheory.DerivedCategory.IdealPower.Action
