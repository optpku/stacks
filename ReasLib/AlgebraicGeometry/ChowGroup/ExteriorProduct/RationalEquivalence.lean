module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RationalEquivalence

/-- If either of two cycles over a field is rationally trivial, then their exterior product
is rationally trivial. -/
theorem exteriorProduct_isRationallyTrivial_of_left_or_right
    {K : Type u} [Field K] (X Y : SchemeOverField K)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (r s : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (h : @IsRationallyTrivial X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance r α ∨
        @IsRationallyTrivial Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance s β) :
    @IsRationallyTrivial (X ⨯ Y).left
      (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (r + s)
      (CycleGroup.exteriorProductPairing X Y r s α β) := sorry

end AlgebraicGeometry.RationalEquivalence
