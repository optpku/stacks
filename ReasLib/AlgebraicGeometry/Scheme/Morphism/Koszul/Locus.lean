/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If `X` and `Y` are flat and locally of finite presentation over `S`, then the locus
where an `S`-morphism `f : X ⟶ Y` is Koszul is open in `X`. -/
theorem isOpen_koszulAt_locus
    {S X Y : Scheme.{u}} (f : X ⟶ Y) (pX : X ⟶ S) (pY : Y ⟶ S)
    (h_over : f ≫ pY = pX) [Flat pX] [LocallyOfFinitePresentation pX]
    [Flat pY] [LocallyOfFinitePresentation pY] :
    IsOpen {x : X | f.KoszulAt x} := sorry

/-- Under an arbitrary base change, the Koszul locus of a morphism between schemes flat and
locally of finite presentation over the base is the inverse image of its original Koszul locus. -/
theorem koszulAt_locus_eq_preimage_of_baseChange
    {X' X Y' Y S' S : Scheme.{u}} (f' : X' ⟶ Y') (f : X ⟶ Y)
    (pX' : X' ⟶ S') (pX : X ⟶ S) (pY' : Y' ⟶ S') (pY : Y ⟶ S)
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (g : S' ⟶ S)
    (h_over' : f' ≫ pY' = pX') (h_over : f ≫ pY = pX)
    (sq : CommSq f' gX gY f) (hX : IsPullback gX pX' pX g)
    (hY : IsPullback gY pY' pY g) [Flat pX] [LocallyOfFinitePresentation pX]
    [Flat pY] [LocallyOfFinitePresentation pY] :
    {x' : X' | f'.KoszulAt x'} = gX ⁻¹' {x : X | f.KoszulAt x} := sorry

end AlgebraicGeometry.Scheme.Hom
