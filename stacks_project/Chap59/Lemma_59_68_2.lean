module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale.Small
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 59.68.2: for a smooth curve over an algebraically closed field, the higher
direct images R^q j_* Gₘ on the generic point vanish for every q ≥ 1. -/
@[stacks 03RJ] #check
  (AlgebraicGeometry.SchemeOverField.genericUnits_higherDirectImage_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify
      (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasInjectiveResolutions
      (Sheaf (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
        AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q),
    IsZero
      (higherDirectImage
        (smallEtalePullback (X.left.fromSpecResidueField (genericPoint X.left)))
        (unitsAddSheaf (Spec (X.left.residueField (genericPoint X.left)))) q :
        Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))

end AlgebraicGeometry.SchemeOverField
