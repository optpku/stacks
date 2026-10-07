module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.LocalizationQuotient

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- Lemma 110.79.1: there exists a morphism `X ⟶ Y` of affine schemes which is
universally submersive such that `{X ⟶ Y}` is not a V covering. -/
@[stacks 0EU9] #check
  (AlgebraicGeometry.exists_affine_universallySubmersive_not_isVCovering :
    ∃ (X Y : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine Y) (f : X ⟶ Y),
      UniversallySubmersive f ∧
        ¬ IsVCovering Y (fun _ : PUnit ↦ X) (fun _ ↦ f))

end AlgebraicGeometry
