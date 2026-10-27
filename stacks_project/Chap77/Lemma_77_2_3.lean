/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Impurity.Limits

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.2.3: An impurity over a directed inverse limit of affine schemes
descends to an impurity at some stage. -/
@[stacks 0CV9] #check (AlgebraicGeometry.AlgebraicSpace.Modules.IsImpurity.exists_stage :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    (f : X ⟶ Y) → [FiniteType f] → [Decent f] → (F : X.Modules) →
    [F.IsQuasicoherent] → [F.IsFiniteType] → (y : Points Y) →
    {I : Type u} → [Preorder I] → [Nonempty I] → [IsDirected I (· ≤ ·)] →
    (D : OrderDual I ⥤ SchemeOver Y) →
    (hAff : ∀ i, IsAffine (D.obj i).left.left) → (c : Cone D) → (hc : IsLimit c) →
    (t' t : c.pt.left.left) → (ξ : Points (Limits.pullback f c.pt.hom)) →
    (h : IsImpurity f F y c.pt t' t ξ) →
    ∃ i, IsImpurity f F y (D.obj i) ((c.π.app i).left.left t')
      ((c.π.app i).left.left t) (Points.map (baseChangeSpaceMap f (c.π.app i)) ξ))
