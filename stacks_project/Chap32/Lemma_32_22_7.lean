module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 32.22.7: in the common-tail finite-presentation approximation setup, a smooth limit
morphism induces smooth descended morphisms at every sufficiently late stage. -/
@[stacks 0CNU] #check
  (AlgebraicGeometry.FinitePresentationApproximationLimitSystem.exists_eventually_smooth :
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
      [AlgebraicGeometry.Scheme.Hom.FiniteType xToS]
      [AlgebraicGeometry.QuasiSeparated yToS]
      [AlgebraicGeometry.Scheme.Hom.FiniteType yToS]
      (Xapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₀ Xsys xCone xToS)
      (Yapprox : AlgebraicGeometry.FinitePresentationApproximationLimitSystem
        D c i₀ Ysys yCone yToS)
      (φ : AlgebraicGeometry.InverseSystemMorphismOverBase
        D i₀ Xsys Ysys xToBase yToBase)
      (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
      (hφ : φ.IsLimitMorphism xCone yCone f) (hf_smooth : AlgebraicGeometry.Smooth f),
      ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
        AlgebraicGeometry.Smooth
          (φ.hom.app (AlgebraicGeometry.tailObject i (le_trans hi₀i₃ hi₃i))))
