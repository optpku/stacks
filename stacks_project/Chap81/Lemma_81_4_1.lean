/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Descent
import StacksCheckRecall

/-!
# Lemma 81.4.1

The functor from sheaves on the small étale site of an algebraic space to
descent data for étale sheaves along an étale covering is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.4.1: Let `S` be a scheme. Let `{f i : Xᵢ i ⟶ X}` be an étale covering
of algebraic spaces. The functor `Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
etaleCoveringDescent f` is an equivalence of categories. -/
@[stacks 0GFS] #check
  (AlgebraicGeometry.AlgebraicSpace.sheafToEtaleCoveringDescent_isEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type u}
    {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)],
    (⋃ i, Set.range (Points.map (f i))) = Set.univ →
    (sheafToEtaleCoveringDescent f).IsEquivalence)
