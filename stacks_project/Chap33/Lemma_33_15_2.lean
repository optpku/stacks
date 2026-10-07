module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.QuasiAffine

@[expose] public section

open AlgebraicGeometry CommRingCat CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 33.15.2: quasi-affineness of a scheme over a field descends from its base change
along an arbitrary field extension. -/
@[stacks 0BDD] #check
  (AlgebraicGeometry.Scheme.Hom.isQuasiAffine_of_isQuasiAffine_baseChangeToFieldExtension :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : Scheme.{u}} (f : X ⟶ Spec (of k)),
      (FieldExtension.baseChange k K f).IsQuasiAffine → X.IsQuasiAffine)

end AlgebraicGeometry.Scheme.Hom
