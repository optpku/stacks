/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Cartesian

/-!
# Cartesian sheaves on the Zariski site of a simplicial space

The cartesianness predicate and augmentation functors are provided by the shared
simplicial sheaf API.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.SimplicialObject
open scoped Simplicial

variable (Y : SimplicialObject TopCat.{u})
variable (A : Type (u + 1)) [Category.{u} A]
variable [∀ n : ℕ, HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) A]
variable [HasWeakSheafify (zariskiTopology Y) A]
variable [HasOpensMapLeftKanExtension Y A]

#check (CategoryTheory.SimplicialObject.IsCartesianSheaf Y A :
  Sheaf (zariskiTopology Y) A → Prop)
