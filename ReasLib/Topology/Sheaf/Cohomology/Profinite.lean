/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Cohomology.Exact
public import ReasLib.Topology.Sheaf.GlobalSections.Profinite
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of profinite spaces

This file specializes exactness of profinite global sections to both objectwise cohomology on the
top open and canonical global cohomology.  The source-facing statement uses the bundled
`Profinite`; class-based companions apply directly to any suitably structured `TopCat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.Profinite

/-- Positive-degree objectwise cohomology on the top open vanishes on a compact Hausdorff totally
disconnected space. -/
@[stacks 0A3F "class-based profinite cohomology vanishing"]
theorem isZero_atTop {X : TopCat.{u}} [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (F : X.Sheaf AddCommGrpCat.{u})
    {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q (⊤ : Opens X)) := sorry

/-- Positive-degree canonical global cohomology vanishes on a compact Hausdorff totally
disconnected space. -/
@[stacks 0A3F "class-based profinite global cohomology vanishing"]
theorem isZero_global {X : TopCat.{u}} [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] (F : X.Sheaf AddCommGrpCat.{u})
    {q : ℕ} (hq : 0 < q) :
    IsZero ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology X) q).obj F) := sorry

/-- Lemma 20.22.3 (0A3F): every abelian sheaf on a profinite space has vanishing global
cohomology in positive degree. -/
@[stacks 0A3F]
theorem isZero_higherCohomology
    {X : _root_.Profinite.{u}} (F : X.toTop.Sheaf AddCommGrpCat.{u})
    {q : ℕ} (hq : 0 < q) :
    IsZero (F.H' q (⊤ : Opens X.toTop)) := sorry

end TopCat.Sheaf.Cohomology.Profinite
