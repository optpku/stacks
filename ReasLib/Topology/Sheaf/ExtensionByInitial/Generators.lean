/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.ExtensionByInitial.Basic
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import Mathlib.Topology.Sheaves.AddCommGrpCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Opens.Subspace

noncomputable section

universe u

namespace TopCat.Sheaf.ExtensionByInitial.AddCommGrp

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The abelian sheaf obtained by extending the constant integer sheaf on an open subspace
by the initial object. -/
noncomputable abbrev constantInteger (U : Opens X) : X.Sheaf AddCommGrpCat.{u} :=
  (j! U).obj (CategoryTheory.constantIntegerSheaf (Opens.grothendieckTopology (space U)))

/-- Every abelian sheaf is an epimorphic image of a coproduct of extensions by the initial
object of constant integer sheaves on open subspaces. -/
theorem existsEpiFromCoproduct (F : X.Sheaf AddCommGrpCat.{u}) :
    ∃ (I : Type u) (U : I → Opens X)
      (φ : (∐ fun i : I ↦ constantInteger (U i)) ⟶ F), Epi φ := sorry

end TopCat.Sheaf.ExtensionByInitial.AddCommGrp

end

end
