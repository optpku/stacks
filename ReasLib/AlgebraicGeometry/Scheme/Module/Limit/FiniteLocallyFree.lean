/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.FinitePresentation

/-!
# Finite locally free modules over inverse limits of schemes

Finite locally free modules descend along directed inverse limits of quasi-compact,
quasi-separated schemes with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Limit.FiniteLocallyFree

/-- A finite locally free module on a directed inverse limit of quasi-compact,
quasi-separated schemes with affine transition maps descends to a finite locally free module
at some stage. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules) [ℱ.IsFiniteLocallyFree] :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      ℱi.IsFiniteLocallyFree ∧
        Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.Limit.FiniteLocallyFree
