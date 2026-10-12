/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {B : Set (Opens X)} {hB : Opens.IsBasis B}
variable (𝒪 : BasisSiteSheaf CommRingCat.{u} B)
variable (ℱ : SheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm
  (J := basisGrothendieckTopology B) 𝒪))

/- Lemma 6.30.12: the canonical extension of a module sheaf on a topological basis carries a
module structure over the extension of the ring sheaf, agreeing with the original action on basis
opens. -/
@[stacks 009T]
#check (BasisSiteSheaf.extendModuleOfComm_of_isBasis hB 𝒪 ℱ)
