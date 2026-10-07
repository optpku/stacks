module

public import stacks_project.Chap70.Lemma_70_23_4_Morphism
public import stacks_project.Chap70.Lemma_70_23_4_LimitSystem
import StacksCheckRecall

/-!
# Lemma 70.23.4

A morphism of quasi-separated finite-type algebraic spaces over a directed
affine limit descends to the associated finite-type approximation systems on a
common tail, and any two such descents inducing the original morphism agree on a
sufficiently late tail.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.23.4 (1): in Situation 70.23.1, a morphism f : X ⟶ Y of algebraic
spaces quasi-separated and of finite type over B, together with good diagrams as
in 70.23.2.1 and the corresponding Lemma 70.23.3 limit descriptions, descends to
a morphism of inverse systems over (B_i) on a common tail with f = lim f_i. -/
@[stacks 0CPA] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_morphism :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {i₁ i₂ : I}
      {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
      {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToBase : Xsys ⟶ tailBaseDiagram D i₁) (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
        xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
        yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
      [QuasiSeparated xToS] [FiniteType xToS]
      [QuasiSeparated yToS] [FiniteType yToS]
      (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
      (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS),
      ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
        ∃ φ : InverseSystemMorphismOverBase D i₀
          (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
          (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
          φ.IsLimitMorphism
            (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
            (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f)

/- Lemma 70.23.4 (2): any two morphisms of inverse systems over (B_i) on a common
tail that both induce f agree for all sufficiently late stages. -/
@[stacks 0CPA] #check
  (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.eventually_eq_of_isLimitMorphism :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {i₁ i₂ : I}
      {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
      {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
      (xCone : Cone Xsys) (yCone : Cone Ysys)
      (xToBase : Xsys ⟶ tailBaseDiagram D i₁) (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
      (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
        xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
        yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
      [QuasiSeparated xToS] [FiniteType xToS]
      [QuasiSeparated yToS] [FiniteType yToS]
      (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
      (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
      {i₀ : I} (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
      (φ ψ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase)),
      φ.IsLimitMorphism
          (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
          (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f →
        ψ.IsLimitMorphism
          (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
          (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f →
        ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
          φ.hom.app (tailObject j (le_trans hi₀i hij)) =
            ψ.hom.app (tailObject j (le_trans hi₀i hij)))
