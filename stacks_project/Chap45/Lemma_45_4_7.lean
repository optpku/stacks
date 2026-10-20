module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowMotive.ProjectiveLine

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

universe u

/- Lemma 45.4.7: in the category of Chow motives over `k`, the motive of `ℙ¹_k`
is isomorphic to the biproduct of the tensor unit and its Tate twist by `-1`. -/
@[stacks 0FGG]
#check (ChowMotive.ProjectiveLine.decomposition :
  {k : Type u} → [Field k] →
    ChowMotive.h (ProjectiveSpace.schemeOver k 1) ≅
      𝟙_ (ChowMotive k (fun _ ↦ Correspondence.GradedCategory k)) ⊞
        ChowMotive.tateTwist (SchemeOverField.point k) (-1))
