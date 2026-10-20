module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation
import StacksCheckRecall

/-!
# Lemma 32.22.4

The tail-system and finite-type approximation API is owned by
`ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation`.

@stack 0CNR
-/

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.22.4: a morphism between quasi-separated finite-type schemes over a directed affine
limit descends to the associated finite-presentation approximation systems on a common tail, and
any two such descents inducing the original morphism agree on a sufficiently late tail. -/
@[stacks 0CNR] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_morphism_eventually_unique :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, AlgebraicGeometry.IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hjj'))]
      {i₁ i₂ : I}
      {Xsys : Over (show OrderDual I from i₁) ⥤ AlgebraicGeometry.Scheme.{u}}
      {Ysys : Over (show OrderDual I from i₂) ⥤ AlgebraicGeometry.Scheme.{u}}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToBase : Xsys ⟶ AlgebraicGeometry.tailBaseDiagram D i₁)
      (yToBase : Ysys ⟶ AlgebraicGeometry.tailBaseDiagram D i₂)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
        xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
        yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
      [AlgebraicGeometry.QuasiSeparated xToS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType xToS]
      [AlgebraicGeometry.QuasiSeparated yToS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType yToS]
      (Xapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₁ Xsys xCone xToS)
      (Yapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₂ Ysys yCone yToS)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS),
      ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
        ∃ φ : AlgebraicGeometry.InverseSystemMorphismOverBase D i₀
          (AlgebraicGeometry.restrictTail hi₁ Xsys)
          (AlgebraicGeometry.restrictTail hi₂ Ysys)
          (AlgebraicGeometry.restrictTailToBase D hi₁ xToBase)
          (AlgebraicGeometry.restrictTailToBase D hi₂ yToBase),
          φ.IsLimitMorphism (Cone.whisker
            (Over.map (homOfLE hi₁ :
              (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁))) xCone)
            (Cone.whisker
              (Over.map (homOfLE hi₂ :
                (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂))) yCone) f ∧
          ∀ ψ : AlgebraicGeometry.InverseSystemMorphismOverBase D i₀
              (AlgebraicGeometry.restrictTail hi₁ Xsys)
              (AlgebraicGeometry.restrictTail hi₂ Ysys)
              (AlgebraicGeometry.restrictTailToBase D hi₁ xToBase)
              (AlgebraicGeometry.restrictTailToBase D hi₂ yToBase),
            ψ.IsLimitMorphism (Cone.whisker
              (Over.map (homOfLE hi₁ :
                (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁))) xCone)
              (Cone.whisker
                (Over.map (homOfLE hi₂ :
                  (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂))) yCone) f →
              ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
                φ.hom.app (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)) =
                  ψ.hom.app (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)))
