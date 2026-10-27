/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # Coproducts from clopen covers of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A small pairwise disjoint clopen cover of the points of an algebraic space by
open subspaces exhibits the space as their coproduct via the canonical map. -/
theorem isIso_coproductDesc_of_clopen_cover
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v} [Small.{u} I]
    (U : I → OpenSubspace X)
    (h_cover : (⋃ i, (U i).pointsSet) = Set.univ)
    (h_disjoint : Pairwise (fun i j ↦ Disjoint (U i).pointsSet (U j).pointsSet))
    (h_clopen : ∀ i, IsClopen (U i).pointsSet) :
    IsIso (coproductDesc fun i ↦ (U i).ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
