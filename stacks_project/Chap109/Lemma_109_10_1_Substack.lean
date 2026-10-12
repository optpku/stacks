/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus
public import stacks_project.Chap99.Situation_99_15_1_Category
public import stacks_project.Chap109.Lemma_109_9_1_Substack

/-!
# The object property of geometrically reduced families of curves

`𝒞urves^{geomred}` is the full subcategory of families of curves whose fibres
are geometrically reduced in the sense of Definition 76.29.2. Membership is the
source-facing packaging of a classifying morphism factoring through that open
substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves with geometrically reduced fibres,
corresponding to the open substack 𝒞urves^{geomred}. -/
def geometricallyReduced (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P)

/-- Membership in `geometricallyReduced` means every fibre of the structure
morphism is geometrically reduced. -/
theorem geometricallyReduced_iff {S : Scheme.{u}} (P : Obj S) :
    geometricallyReduced S P ↔
      ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P) :=
  sorry

/-- The geometrically reduced property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_geometricallyReduced (S : Scheme.{u}) :
    (geometricallyReduced S).IsClosedUnderIsomorphisms :=
  sorry


end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
