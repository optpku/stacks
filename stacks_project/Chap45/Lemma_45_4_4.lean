module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowMotive.ProjectiveLine

@[expose] public section

open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

universe u

/- Lemma 45.4.4
With notation as in Example 45.3.7 the motive `(X, c₀, 0)` is isomorphic to the
motive `𝟙 = (Spec k, 1, 0)`. The motive `(X, c₂, 0)` is isomorphic to the motive
`𝟙(-1) = (Spec k, 1, -1)`. -/
@[stacks 0FGD]
#check (ChowMotive.ProjectiveLine.pointProjectorIsoUnit :
  {k : Type u} → [Field k] →
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
      ChowMotive.ProjectiveLine.pointProjectorMotive x ≅
        𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)))

#check (ChowMotive.ProjectiveLine.tateProjectorIsoTwist :
  {k : Type u} → [Field k] →
    (x : SchemeOverField.point k ⟶ ProjectiveSpace.schemeOver k 1) →
      ChowMotive.ProjectiveLine.tateProjectorMotive x ≅
        ChowMotive.tateTwist (SchemeOverField.point k) (-1))
