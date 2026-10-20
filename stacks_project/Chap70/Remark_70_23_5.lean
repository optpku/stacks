/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.Equivalence
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

/- Remark 70.23.5: quasi-separated finite-type algebraic spaces over a directed
limit of Noetherian algebraic spaces with affine transitions are equivalent to
admissible approximation systems with comparison morphisms modulo eventual equality. -/
@[stacks 0CPB] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation.limitFunctor_isEquivalence :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))],
      (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximation.limitFunctor D c).IsEquivalence)

-- The identity-induced comparisons between two descriptions become mutually inverse.
#check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_morphisms_eventually_inverse :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      (X : AlgebraicSpace S) {i₁ i₂ : I}
      {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
      {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
      (xπ : (Functor.const (Over (OrderDual.toDual i₁))).obj X ⟶ Xsys)
      (yπ : (Functor.const (Over (OrderDual.toDual i₂))).obj X ⟶ Ysys)
      (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
      (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
      (toS : X ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
        xπ.app j ≫ xToBase.app j = toS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
        yπ.app j ≫ yToBase.app j = toS ≫ c.π.app j.left)
      [QuasiSeparated toS] [FiniteType toS]
      (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys
        (⟨X, xπ⟩ : Cone Xsys) toS)
      (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys
        (⟨X, yπ⟩ : Cone Ysys) toS),
      ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
        ∃ φ : InverseSystemMorphismOverBase D i₀
            (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
            (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
          φ.IsLimitMorphism
            (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁))
              (⟨X, xπ⟩ : Cone Xsys))
            (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂))
              (⟨X, yπ⟩ : Cone Ysys)) (𝟙 X) ∧
          ∃ ψ : InverseSystemMorphismOverBase D i₀
              (restrictTail hi₂ Ysys) (restrictTail hi₁ Xsys)
              (restrictTailToBase D hi₂ yToBase) (restrictTailToBase D hi₁ xToBase),
            ψ.IsLimitMorphism
              (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂))
                (⟨X, yπ⟩ : Cone Ysys))
              (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁))
                (⟨X, xπ⟩ : Cone Xsys)) (𝟙 X) ∧
            ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ {j : I} (hij : i ≤ j),
              (InverseSystemMorphismOverBase.comp φ ψ).hom.app
                  (tailObject j (le_trans hi₀i hij)) = 𝟙 _ ∧
              (InverseSystemMorphismOverBase.comp ψ φ).hom.app
                  (tailObject j (le_trans hi₀i hij)) = 𝟙 _)
