module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Smooth

/-!
# Smooth morphisms in finite-type approximation systems

Smooth morphisms between the limits of finite-presentation approximation systems are smooth on
a sufficiently late common tail. Smooth morphisms between affine schemes also descend to smooth
finite-type approximation diagrams over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.FinitePresentationApproximationLimitSystem

/-- A descended morphism between finite-presentation approximation systems that induces a smooth
morphism on their limits is smooth at every sufficiently late stage. -/
theorem exists_eventually_smooth
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₀ : I}
    {Xsys Ysys : TailIndexCategory i₀ ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₀)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₀)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : TailIndexCategory i₀,
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : TailIndexCategory i₀,
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [Scheme.Hom.FiniteType xToS]
    [QuasiSeparated yToS] [Scheme.Hom.FiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₀ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₀ Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hφ : φ.IsLimitMorphism xCone yCone f) (hf_smooth : Smooth f) :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
      Smooth (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))) := sorry

end AlgebraicGeometry.FinitePresentationApproximationLimitSystem

namespace AlgebraicGeometry.FiniteTypeApproximationDiagram

/-- A smooth morphism between affine schemes is obtained by base change from a smooth finite-type
morphism between affine schemes over `Spec ℤ`. -/
theorem exists_isPullback_of_smooth
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Smooth f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (π : S ⟶ S₀)
      (_ : Scheme.Hom.FiniteType (specULiftZIsTerminal.from S₀))
      (D : FiniteTypeApproximationDiagram f π) (_ : IsAffine D.W)
      (_ : Scheme.Hom.FiniteType D.toSi) (_ : Smooth D.toSi),
      IsPullback D.toW f D.toSi π := sorry

end AlgebraicGeometry.FiniteTypeApproximationDiagram
