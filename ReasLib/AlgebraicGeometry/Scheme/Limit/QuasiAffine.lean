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

/-- In a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms, if a specified limit is quasi-affine, then all sufficiently late stages
are quasi-affine. -/
theorem exists_eventually_isQuasiAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (hS : c.pt.IsQuasiAffine) :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.Limit
