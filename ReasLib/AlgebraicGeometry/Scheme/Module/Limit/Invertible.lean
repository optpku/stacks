/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.FiniteLocallyFree

/-!
# Invertible modules over inverse limits of schemes

Invertible modules descend along directed inverse limits of quasi-compact, quasi-separated
schemes with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Limit.Invertible

/-- An invertible module on a directed inverse limit of quasi-compact, quasi-separated schemes
with affine transition maps descends to an invertible module at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (ℒ : c.pt.Modules) [Scheme.Modules.Invertible ℒ] :
    ∃ (i : I) (ℒi : (D.obj i).Modules),
      Scheme.Modules.Invertible ℒi ∧
        Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℒi ≅ ℒ) := sorry

end AlgebraicGeometry.Scheme.Modules.Limit.Invertible
