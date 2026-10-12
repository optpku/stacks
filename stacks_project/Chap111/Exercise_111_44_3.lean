/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Surface.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Exercise 111.44.3: over an algebraically closed field `k`, a projective
surface `X` admits a proper closed subscheme `Z ⊂ X`, recorded as
`Z : X.left.IdealSheafData` with `Z.support ≠ ⊤`, such that `H¹(Z, 𝒪_Z)` is
nonzero. -/
@[stacks 0DB6] #check
  (AlgebraicGeometry.SchemeOverField.exists_properClosedSubscheme_firstCohomology_structureSheaf_not_isZero :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom],
    topologicalKrullDim X.left = 2 →
    ∃ Z : X.left.IdealSheafData, Z.support ≠ ⊤ ∧
      ¬ IsZero (Scheme.Hom.cohomology (Z.subschemeι ≫ X.hom)
          (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules) 1))
