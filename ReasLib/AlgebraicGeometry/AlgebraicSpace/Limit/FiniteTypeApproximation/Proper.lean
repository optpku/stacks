module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Proper morphisms in finite-type approximation systems of algebraic spaces

A proper morphism between the limits of finite-type approximation systems of
algebraic spaces is proper on a sufficiently late common tail.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteTypeApproximationLimitSystem

/-- A proper morphism between the limits of finite-type approximation systems of
algebraic spaces is proper at every sufficiently late stage. -/
@[stacks 0CPE]
theorem exists_eventually_proper
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₀ : I}
    {Xsys Ysys : Over (OrderDual.toDual i₀) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₀)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₀)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (OrderDual.toDual i₀),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₀ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₀ Ysys yCone yToS)
    (φ : InverseSystemMorphismOverBase D i₀ Xsys Ysys xToBase yToBase)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    (hf_limit : φ.IsLimitMorphism xCone yCone f)
    [Proper f] :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
      Proper (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))) := sorry

end FiniteTypeApproximationLimitSystem

end AlgebraicGeometry.AlgebraicSpace
