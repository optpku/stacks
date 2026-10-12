/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.Surjectivity
public import ReasLib.Topology.Opens.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofinal Cech vanishing for modules on a ringed space

This leaf specializes the site-level degreewise predicate and its degree-one surjectivity theorem
through the canonical underlying additive sheaf of a module.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}}

/-- A module sheaf has cofinally vanishing degree-`p` Cech cohomology at an open subset when its
underlying additive sheaf has the site-level property. -/
@[stacks 01EU "cofinal module Cech vanishing"]
abbrev VanishesCofinally
    (F : X.Modules) (U : Opens X.carrier) (p : ℕ) : Prop :=
  CategoryTheory.Sheaf.Cech.VanishesCofinally.{u}
    ((moduleUnderlyingSheaf X).obj F) U p

namespace VanishesCofinally

/-- Lemma 20.11.7 (01EU): cofinal vanishing of first Cech cohomology of the left term makes the
right map of a short exact sequence surjective on sections over the chosen open. -/
@[stacks 01EU "surjectivity of module sections from cofinal Cech vanishing"]
theorem surjective_right
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    {U : Opens X.carrier} (hF : VanishesCofinally S.X₁ U 1) :
    Function.Surjective
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map S.g) := sorry

end VanishesCofinally

end AlgebraicGeometry.RingedSpace.ModuleCech
