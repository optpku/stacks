module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.22.8: a morphism between finite-presentation approximation systems that induces a
proper morphism on their limits is proper at every sufficiently late stage. -/
@[stacks 0CNV] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_eventually_isProper :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, AlgebraicGeometry.IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hjj'))]
      {i₁ i₂ : I}
      {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicGeometry.Scheme.{u}}
      {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicGeometry.Scheme.{u}}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToBase : Xsys ⟶ AlgebraicGeometry.tailBaseDiagram D i₁)
      (yToBase : Ysys ⟶ AlgebraicGeometry.tailBaseDiagram D i₂)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
        xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
        yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
      [AlgebraicGeometry.QuasiSeparated xToS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType xToS]
      [AlgebraicGeometry.QuasiSeparated yToS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType yToS]
      (Xapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₁ Xsys xCone xToS)
      (Yapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₂ Ysys yCone yToS)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
      [AlgebraicGeometry.IsProper f]
      (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
      (φ : AlgebraicGeometry.InverseSystemMorphismOverBase D i₀
        (AlgebraicGeometry.restrictTail hi₁ Xsys)
        (AlgebraicGeometry.restrictTail hi₂ Ysys)
        (AlgebraicGeometry.restrictTailToBase D hi₁ xToBase)
        (AlgebraicGeometry.restrictTailToBase D hi₂ yToBase))
      (hφ : φ.IsLimitMorphism (Cone.whisker
        (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
        (Cone.whisker
          (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f),
      ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
        AlgebraicGeometry.IsProper
          (φ.hom.app (AlgebraicGeometry.tailObject i (le_trans hi₀i₃ hi₃i))))
