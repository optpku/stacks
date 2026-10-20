/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Cohomology.Bridge
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.Types.Constant
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Irreducible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant-sheaf cohomology on irreducible spaces

@stack 02UW

On an irreducible space, every locally constant section on a nonempty open is constant.  The
resulting surjective restriction maps make a constant additive sheaf flasque.  This leaf exposes
that reusable property and its canonical positive-degree cohomology consequence without requiring
consumers to install sheafification, Grothendieck, or `HasExt` instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Constant

variable {X : TopCat.{u}}

/-- A constant sheaf of additive commutative groups on an irreducible space is flasque. -/
@[stacks 02UW "constant additive sheaves on irreducible spaces are flasque"]
noncomputable instance isFlasque_of_irreducible [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf.IsFlasque
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A) := sorry

/-- Lemma 20.20.2 (02UW): a constant additive sheaf on an irreducible space has zero
positive-degree global cohomology. -/
@[stacks 02UW "higher cohomology of a constant sheaf on an irreducible space"]
theorem isZero_cohomology [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) {p : ℕ} (hp : 0 < p) :
    IsZero
      (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).H' p
        (⊤ : Opens X)) := sorry

end TopCat.Sheaf.Constant

end
