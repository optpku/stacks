module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.Topology.Sheaves.Simplicial.Cartesian

/-!
# Weak Serre closure of cartesian abelian sheaves

Cartesian abelian sheaves on the Zariski site of a simplicial space form a weak
Serre subcategory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}}
variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [∀ n : ℕ, HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}]

/-- Cartesian abelian sheaves on `Y_Zar` form a weak Serre subcategory of
`Ab(Y_Zar)`. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass (cartesianProperty Y AddCommGrpCat.{u}) :=
  sorry

end CategoryTheory.SimplicialObject
