/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap103.Lemma_103_10_1_FromGroupoid
public import stacks_project.Chap103.Lemma_103_10_1_Descent

/-!
# Right adjoint to the inclusion of quasi-coherent modules into LQCoh^{fbc}

On an algebraic stack `X`, the functor `Q : LQCoh^{fbc}(𝒪_X) ⥤ QCoh(𝒪_X)` is
the composite of descent to the chosen smooth presenting groupoid, the inverse
of `toGroupoidEquivalence`, and inverse pullback along the presentation
`1`-morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Pullback of quasi-coherent modules along the `1`-morphism of the chosen
smooth presentation of an algebraic stack is an equivalence. -/
instance QCoh.presentationPullback_isEquivalence (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (QCoh.pullback (algebraicStackPresentation X).hom).IsEquivalence :=
  sorry

/-- The functor `Q : LQCoh^{fbc}(𝒪_X) ⥤ QCoh(𝒪_X)` obtained as `q₂` followed by
`fromGroupoid` and inverse pullback along the chosen smooth presentation. -/
def LQCohFbc.toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc X ⥤ QCoh X :=
  LQCohFbc.toGroupoidModules X ⋙
    QCoh.fromGroupoidStack (algebraicStackPresentation X).groupoid ⋙
      (QCoh.pullback (algebraicStackPresentation X).hom).inv

/-- `toQCoh` is descent to the presenting groupoid, followed by `fromGroupoid`
and inverse pullback along the presentation. -/
theorem LQCohFbc.toQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    LQCohFbc.toQCoh X =
      LQCohFbc.toGroupoidModules X ⋙
        QCoh.fromGroupoidStack (algebraicStackPresentation X).groupoid ⋙
          (QCoh.pullback (algebraicStackPresentation X).hom).inv :=
  sorry

/-- The inclusion `toLQCohFbc` is left adjoint to the constructed functor
`toQCoh`. -/
theorem QCoh.toLQCohFbc_isRightAdjoint_toQCoh (X : GroupoidsOver S)
    [AlgebraicStack X] :
    Nonempty (QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
