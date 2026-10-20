/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FactorSwap
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Exchange the factors of a product on a fixed-dimensional Chow group. -/
noncomputable def swapEquiv {k : Type u} [Field k]
    (X Y : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (n : ℤ) :
    @ChowGroup (X ⨯ Y).left
        (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n ≃+
      @ChowGroup (Y ⨯ X).left
        (LocallyOfFiniteType.isLocallyNoetherian (Y ⨯ X).hom)
        ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n where
  toFun := map (fun _ ↦ 0) (X ⨯ Y) (Y ⨯ X) (Limits.prod.braiding X Y).hom n
  invFun := map (fun _ ↦ 0) (Y ⨯ X) (X ⨯ Y) (Limits.prod.braiding X Y).inv n
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- Factor exchange carries a represented Chow class to the class of the exchanged cycle. -/
theorem swapEquiv_chowClass {k : Type u} [Field k]
    (X Y : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (n : ℤ)
    (z : CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) n) :
    swapEquiv X Y n
        (@chowClass (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n z) =
      @chowClass (Y ⨯ X).left (LocallyOfFiniteType.isLocallyNoetherian (Y ⨯ X).hom)
        ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
        (CycleGroup.mapHom (Limits.prod.braiding X Y).hom.left
          ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
          ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) n z) := sorry

end AlgebraicGeometry.ChowGroup
