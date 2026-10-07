module

import ReasLib.AlgebraicGeometry.Scheme.Module.Surface.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Exercise 111.44.4: over an algebraically closed field `k`, a projective
surface `X` admits, for every `n : ℕ`, a proper closed subscheme `Z ⊂ X`,
recorded as `Z : X.left.IdealSheafData` with `Z.support ≠ ⊤`, such that
`n < dim_k H¹(Z, 𝒪_Z)`. -/
@[stacks 0DB7] #check
  (AlgebraicGeometry.SchemeOverField.exists_properClosedSubscheme_firstCohomology_structureSheaf_finrank_gt :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [Projective X.hom],
      topologicalKrullDim X.left = 2 → (n : ℕ) →
        ∃ Z : X.left.IdealSheafData, Z.support ≠ ⊤ ∧
          n < Scheme.Hom.cohomologyFinrank (Z.subschemeι ≫ X.hom)
              (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1)

end AlgebraicGeometry.SchemeOverField
