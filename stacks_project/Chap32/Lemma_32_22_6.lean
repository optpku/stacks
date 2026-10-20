/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.22.6: in the common-tail approximation setup, a flat finite-presentation limit
morphism is eventually flat and is obtained by cartesian base change from a fixed stage. -/
@[stacks 0CNT] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_flatBaseChange :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, AlgebraicGeometry.IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hjj'))]
      {i₀ : I}
      {Xsys Ysys : AlgebraicGeometry.TailIndexCategory i₀ ⥤ AlgebraicGeometry.Scheme.{u}}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToBase : Xsys ⟶ AlgebraicGeometry.tailBaseDiagram D i₀)
      (yToBase : Ysys ⟶ AlgebraicGeometry.tailBaseDiagram D i₀)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      (xCone_toBase : ∀ j : AlgebraicGeometry.TailIndexCategory i₀,
        xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : AlgebraicGeometry.TailIndexCategory i₀,
        yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
      [AlgebraicGeometry.QuasiSeparated xToS]
      [AlgebraicGeometry.QuasiCompact xToS]
      [AlgebraicGeometry.LocallyOfFiniteType xToS]
      [AlgebraicGeometry.QuasiSeparated yToS]
      [AlgebraicGeometry.QuasiCompact yToS]
      [AlgebraicGeometry.LocallyOfFiniteType yToS]
      (Xapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₀ Xsys xCone xToS)
      (Yapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₀ Ysys yCone yToS)
      (φ : AlgebraicGeometry.InverseSystemMorphismOverBase
        D i₀ Xsys Ysys xToBase yToBase)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
      (hf_limit : φ.IsLimitMorphism xCone yCone f)
      (hflat : AlgebraicGeometry.Flat f)
      (hfp : AlgebraicGeometry.Scheme.Hom.FinitePresentation f),
      ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃),
        AlgebraicGeometry.InverseSystemMorphismOverBase.FlatBaseChangeAt
          hi₀i₃ xCone yCone φ f)
