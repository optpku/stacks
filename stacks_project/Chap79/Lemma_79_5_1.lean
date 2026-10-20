/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Conormal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 79.5.1: An infinitesimal source section of a groupoid with flat source
and target induces the identity on the conormal sheaf of an invariant
first-order thickening. -/
@[stacks 0CKD] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.InfinitesimalSection.conormalMap_eq_id :
    ∀ {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
      {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      {U₀ : AlgebraicSpace S} (ι : U₀ ⟶ G.U.left)
      [IsFirstOrderThickening ι] (δ : GroupoidAlgebraicSpace.InfinitesimalSection G ι)
      [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
      (h_invariant : CategoryTheory.Subobject.IsInvariant G.s.left G.t.left (Subobject.mk ι)),
      GroupoidAlgebraicSpace.InfinitesimalSection.conormalMap G ι δ =
        𝟙 (Hom.conormalSheaf ι))

