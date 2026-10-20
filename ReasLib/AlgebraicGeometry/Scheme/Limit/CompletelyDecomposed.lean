/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A locally finitely presented morphism over one stage of a directed inverse system with
affine transition morphisms is completely decomposed over some later stage if its pullback
to the limit is completely decomposed and its target is quasi-compact and quasi-separated. -/
theorem exists_completelyDecomposed_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i0 : I)
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (X0 Y0 : Over (D.obj i0)) (f0 : X0 ⟶ Y0)
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [LocallyOfFinitePresentation f0.left]
    [Scheme.Hom.CompletelyDecomposed ((Over.pullback (c.π.app i0)).map f0).left] :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.CompletelyDecomposed
        ((Over.pullback (D.map (homOfLE hi0i))).map f0).left := sorry

end AlgebraicGeometry.Scheme.Limit
