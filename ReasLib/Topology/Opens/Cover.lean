/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.Topology.Opens.Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Indexed covers of an open subset

This leaf bridges a lattice presentation `⨆ i, 𝒰 i = U` of an indexed open cover with the
corresponding family in the slice category `Over U` and its site-theoretic covering property.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

universe u v

namespace TopologicalSpace.Opens.Cover

variable {X : Type u} [TopologicalSpace X]

/-- Every member of an indexed family whose supremum is `U` is contained in `U`. -/
theorem le_of_iSup_eq
    (U : Opens X) {ι : Type v} (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U) (i : ι) :
    𝒰 i ≤ U := sorry

/-- An indexed family of opens covering `U`, viewed as a family in `Over U`. -/
def overFamily
    (U : Opens X) {ι : Type v} (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U) :
    ι → Over U :=
  fun i ↦ Over.mk (homOfLE (le_of_iSup_eq U 𝒰 h𝒰 i))

/-- The slice family associated with an indexed cover of `U` covers the terminal object of the
slice site. -/
theorem coversTop_overFamily
    (U : Opens X) {ι : Type v} (𝒰 : ι → Opens X) (h𝒰 : iSup 𝒰 = U) :
    ((Opens.grothendieckTopology X).over U).CoversTop (overFamily U 𝒰 h𝒰) := sorry

end TopologicalSpace.Opens.Cover


