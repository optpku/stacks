/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A compatible family of nonempty closed subsets in a directed inverse system of
quasi-compact, quasi-separated schemes with affine transition morphisms contains the
projections of a point of any specified limit cone. -/
theorem exists_point_mem_closed_of_compatible
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (Z : ∀ i : I, Set (D.obj i))
    (hZ_closed : ∀ i, IsClosed (Z i))
    (hZ_nonempty : ∀ i, (Z i).Nonempty)
    (hZ_compat : ∀ {i i' : I} (hii' : i ≤ i'),
      Set.MapsTo (D.map (homOfLE hii')) (Z i') (Z i)) :
    ∃ s : c.pt, ∀ i, (c.π.app i) s ∈ Z i := sorry

end AlgebraicGeometry.Scheme.Limit
