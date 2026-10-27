/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation

/-!
# Smooth morphisms in finite-type approximation systems of algebraic spaces

A smooth morphism between the limits of finite-type approximation systems of
algebraic spaces is smooth on a sufficiently late common tail.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteTypeApproximationLimitSystem

/-- A smooth morphism between the limits of finite-type approximation systems of
algebraic spaces is smooth at every sufficiently late stage. -/
@[stacks 0CPD]
theorem exists_eventually_smooth
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
    [Smooth f] :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
      Smooth (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))) := sorry

end FiniteTypeApproximationLimitSystem

end AlgebraicGeometry.AlgebraicSpace
