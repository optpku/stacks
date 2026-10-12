/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Remark 32.22.5: two finite-presentation approximation systems of the same quasi-separated
finite-type scheme over a directed affine limit admit identity-induced comparison morphisms in
both directions on a common tail, and these become mutually inverse after further shrinking. -/
@[stacks 0CNS] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_morphisms_eventually_inverse :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, AlgebraicGeometry.IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hjj'))]
      (X : AlgebraicGeometry.Scheme.{u}) {i₁ i₂ : I}
      {Xsys : Over (show OrderDual I from i₁) ⥤ AlgebraicGeometry.Scheme.{u}}
      {Ysys : Over (show OrderDual I from i₂) ⥤ AlgebraicGeometry.Scheme.{u}}
      (xπ : (Functor.const (Over (show OrderDual I from i₁))).obj X ⟶ Xsys)
      (yπ : (Functor.const (Over (show OrderDual I from i₂))).obj X ⟶ Ysys)
      (xToBase : Xsys ⟶ AlgebraicGeometry.tailBaseDiagram D i₁)
      (yToBase : Ysys ⟶ AlgebraicGeometry.tailBaseDiagram D i₂)
      (toS : X ⟶ c.pt)
      (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
        xπ.app j ≫ xToBase.app j = toS ≫ c.π.app j.left)
      (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
        yπ.app j ≫ yToBase.app j = toS ≫ c.π.app j.left)
      [AlgebraicGeometry.QuasiSeparated toS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType toS]
      (Xapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem D c i₁ Xsys
        (⟨X, xπ⟩ : Cone Xsys) toS)
      (Yapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem D c i₂ Ysys
        (⟨X, yπ⟩ : Cone Ysys) toS),
      ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
        ∃ φ : AlgebraicGeometry.InverseSystemMorphismOverBase D i₀
            (AlgebraicGeometry.restrictTail hi₁ Xsys)
            (AlgebraicGeometry.restrictTail hi₂ Ysys)
            (AlgebraicGeometry.restrictTailToBase D hi₁ xToBase)
            (AlgebraicGeometry.restrictTailToBase D hi₂ yToBase),
          φ.IsLimitMorphism (Cone.whisker
            (Over.map (homOfLE hi₁ :
              (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
            (⟨X, xπ⟩ : Cone Xsys))
            (Cone.whisker
              (Over.map (homOfLE hi₂ :
                (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
              (⟨X, yπ⟩ : Cone Ysys)) (𝟙 X) ∧
          ∃ ψ : AlgebraicGeometry.InverseSystemMorphismOverBase D i₀
              (AlgebraicGeometry.restrictTail hi₂ Ysys)
              (AlgebraicGeometry.restrictTail hi₁ Xsys)
              (AlgebraicGeometry.restrictTailToBase D hi₂ yToBase)
              (AlgebraicGeometry.restrictTailToBase D hi₁ xToBase),
            ψ.IsLimitMorphism (Cone.whisker
              (Over.map (homOfLE hi₂ :
                (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
              (⟨X, yπ⟩ : Cone Ysys))
              (Cone.whisker
                (Over.map (homOfLE hi₁ :
                  (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
                (⟨X, xπ⟩ : Cone Xsys)) (𝟙 X) ∧
            ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ {j : I} (hij : i ≤ j),
              (AlgebraicGeometry.InverseSystemMorphismOverBase.comp φ ψ).hom.app
                  (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)) =
                (AlgebraicGeometry.InverseSystemMorphismOverBase.id
                  (D := D) (i0 := i₀)
                  (Xsys := AlgebraicGeometry.restrictTail hi₁ Xsys)
                  (xToBase := AlgebraicGeometry.restrictTailToBase D hi₁ xToBase)).hom.app
                    (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)) ∧
              (AlgebraicGeometry.InverseSystemMorphismOverBase.comp ψ φ).hom.app
                  (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)) =
                (AlgebraicGeometry.InverseSystemMorphismOverBase.id
                  (D := D) (i0 := i₀)
                  (Xsys := AlgebraicGeometry.restrictTail hi₂ Ysys)
                  (xToBase := AlgebraicGeometry.restrictTailToBase D hi₂ yToBase)).hom.app
                    (AlgebraicGeometry.tailObject j (le_trans hi₀i hij)))

end AlgebraicGeometry
