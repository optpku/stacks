/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Immersion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A proper morphism to the limit of a directed inverse system of quasi-compact,
quasi-separated schemes with affine transition morphisms is proper over every sufficiently
late stage, provided its source is locally of finite type over the base scheme. -/
theorem exists_eventually_isProper_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsProper f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsProper (f ≫ c.π.app i) := sorry

end AlgebraicGeometry.Scheme.Limit
