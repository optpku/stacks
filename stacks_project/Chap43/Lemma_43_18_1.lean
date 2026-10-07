module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct.RationalEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Variety
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K]
variable (X Y : SchemeOverField K) [Variety X] [Variety Y]
variable (r s : ℤ)
variable (α : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
variable (β : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)

/- Lemma 43.18.1: for varieties `X` and `Y`, if either cycle `α` on `X` or cycle
`β` on `Y` is rationally equivalent to zero, then their exterior product is rationally
equivalent to zero on `X ⨯ Y`. -/
@[stacks 0B0S] #check
  (AlgebraicGeometry.RationalEquivalence.exteriorProduct_isRationallyTrivial_of_left_or_right
      X Y r s α β :
    (@RationalEquivalence.IsRationallyTrivial X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance r α ∨
        @RationalEquivalence.IsRationallyTrivial Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance s β) →
    @RationalEquivalence.IsRationallyTrivial (X ⨯ Y).left
      (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance (r + s)
      (CycleGroup.exteriorProductPairing X Y r s α β))

end AlgebraicGeometry
