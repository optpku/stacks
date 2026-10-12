/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- Transport between Chow groups whose grading indices are equal. -/
def degreeEquiv {k : Type u} [Field k] (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {m n : ℤ} (h : m = n) :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m ≃+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n :=
  AddEquiv.cast (M := fun q : ℤ ↦
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance q) h

/-- Degree transport acts by equality transport on a Chow class. -/
theorem degreeEquiv_apply {k : Type u} [Field k] (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {m n : ℤ} (h : m = n)
    (c : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance m) :
    degreeEquiv X h c = h ▸ c := sorry

end AlgebraicGeometry.ChowGroup
