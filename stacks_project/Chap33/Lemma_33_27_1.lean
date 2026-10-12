/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section LocallyAlgebraic

variable {k : Type u} [Field k]
variable (X : SchemeOverField k) [LocallyAlgebraic X]

/- Lemma 33.27.1: let `k` be a field and let `X` be a locally algebraic scheme over `k`. The
normalization morphism `X.left.normalizationTo` is finite and dominant; its source is the
coproduct of normal irreducible locally algebraic normalized components; and it factors through
the reduction as the normalization morphism of the reduction. If `X` is reduced algebraic, the
normalization morphism is birational. If `X` is a variety, its normalization is a variety and the
normalization morphism is finite and birational. -/
@[stacks 0BXR] #check
  (SchemeOverField.Normalization.instIsFiniteNormalizationTo X :
    IsFinite X.left.normalizationTo)

#check
  (SchemeOverField.Normalization.instIsDominantNormalizationTo X :
    IsDominant X.left.normalizationTo)

#check
  (SchemeOverField.Normalization.normalizationIsoCoproductIrreducibleComponentNormalizations X :
    ∃ e :
        (∐ fun Z : irreducibleComponents X.left ↦
          (SchemeOverField.Normalization.irreducibleComponentNormalization X Z).left) ≅
            X.left.normalization,
      Limits.Sigma.desc (fun Z : irreducibleComponents X.left ↦
          (X.left.irreducibleComponentSubscheme Z).normalizationTo ≫
            X.left.irreducibleComponentSubschemeι Z) =
        e.hom ≫ X.left.normalizationTo)

#check
  (SchemeOverField.Normalization.isNormal_irreducibleComponentNormalization X :
    ∀ Z : irreducibleComponents X.left,
      Scheme.isNormal
        (SchemeOverField.Normalization.irreducibleComponentNormalization X Z).left)

#check
  (SchemeOverField.Normalization.instIrreducibleSpaceIrreducibleComponentNormalization X :
    ∀ Z : irreducibleComponents X.left,
      IrreducibleSpace
        (SchemeOverField.Normalization.irreducibleComponentNormalization X Z).left)

#check
  (SchemeOverField.Normalization.instLocallyAlgebraicIrreducibleComponentNormalization X :
    ∀ Z : irreducibleComponents X.left,
      LocallyAlgebraic
        (SchemeOverField.Normalization.irreducibleComponentNormalization X Z))

#check
  (Scheme.Normalization.factorsThroughReduction X.left :
    ∃ νred : X.left.normalization ⟶ X.left.reduction,
      νred ≫ X.left.reductionι = X.left.normalizationTo)

#check
  (Scheme.Normalization.reductionFactorIsNormalization X.left :
    ∀ {νred : X.left.normalization ⟶ X.left.reduction},
      νred ≫ X.left.reductionι = X.left.normalizationTo →
        ∃ e : X.left.normalization ≅ X.left.reduction.normalization,
          νred = e.hom ≫ X.left.reduction.normalizationTo)

end LocallyAlgebraic

section ReducedAlgebraic

variable {k : Type u} [Field k]
variable (X : SchemeOverField k) [Algebraic X] [IsReduced X.left]

#check
  (SchemeOverField.Normalization.instIsBirationalNormalizationToOfIsReducedAlgebraic X :
    IsBirational X.left.normalizationTo)

end ReducedAlgebraic

section Variety

variable {k : Type u} [Field k]
variable (X : SchemeOverField k) [Variety X]

#check
  (SchemeOverField.Normalization.instVarietyNormalization X :
    Variety (SchemeOverField.normalization X))

#check
  (SchemeOverField.Normalization.instIsBirationalNormalizationToOfVariety X :
    IsBirational X.left.normalizationTo)

end Variety

end AlgebraicGeometry
