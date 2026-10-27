/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.23.8: in the Lemma 70.23.4 good-diagram setup, a proper morphism of
algebraic spaces is eventually proper on later-stage morphisms. -/
@[stacks 0CPE] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_eventually_proper :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {i₀ : I}
      {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      [QuasiSeparated xToS] [FiniteType xToS]
      [QuasiSeparated yToS] [FiniteType yToS]
      (Xapprox : FiniteTypeApproximationLimitSystem D c i₀ Xsys xCone xToS)
      (Yapprox : FiniteTypeApproximationLimitSystem D c i₀ Ysys yCone yToS)
      (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys Xapprox.toBase Yapprox.toBase)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
      (hf_limit : φ.IsLimitMorphism xCone yCone f)
      [Proper f],
      ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
        Proper (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))))
