/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Pointed.Kernel
import Mathlib.Tactic.CrossRefAttribute

/-!
# The pointed sections-with-support functor

The ambient kernel functor is restricted to the closed subspace. Its functoriality is inherited
from the categorical kernel, so no separate map construction is needed.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

variable {X : TopCat.{u}} {Z : Set X}

/-- Remark 17.6.4 (01B0): the pointed sections-with-support functor for a closed subset. -/
@[stacks 01B0 "pointed sections-with-support functor"]
noncomputable def functor (hZ : IsClosed Z) :
    CategoryTheory.Functor (X.Sheaf Pointed.{u})
      ((TopCat.of Z).Sheaf Pointed.{u}) :=
  ambientFunctor (C := Pointed.{u}) hZ ⋙
    Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)

/-- Evaluating the pointed support functor means restricting the ambient kernel object to `Z`. -/
@[simp]
theorem functor_obj (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (functor hZ).obj F =
      (Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).obj (object hZ F) := sorry

/-- The pointed support functor maps a morphism by the ambient kernel map followed by pullback. -/
@[simp]
theorem functor_map
    (hZ : IsClosed Z) {F G : X.Sheaf Pointed.{u}} (f : F ⟶ G) :
    (functor hZ).map f =
      (Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).map
        ((ambientFunctor (C := Pointed.{u}) hZ).map f) := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

end
