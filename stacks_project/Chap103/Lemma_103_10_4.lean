/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_10_1

/-!
# Restriction of the quasi-coherent adjunction counit along a flat object

On an algebraic stack, the counit `Q(F) ⟶ F` of the adjunction
`QCoh.toLQCohFbc ⊣ LQCohFbc.toQCoh` becomes an isomorphism after restriction
to the small étale site of a flat scheme object.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids Functor.Fiber

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The restriction of the adjunction counit `Q(F) ⟶ F` to the small étale
site of the scheme underlying a fiber object `x`. -/
def LQCohFbc.toQCoh_counit_restrictToSmallEtale
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X)
    (F : LQCohFbc X) :=
  (restrictModulesToSmallEtale X (fiberInclusion.obj x)).map
    ((LQCohFbc.inclusion X).map (adj.counit.app F))

/-- Lemma 103.10.4: on an algebraic stack `X`, if `x` is an object over a
scheme `U` such that `x : U ⟶ X` is flat, then for `F` in `LQCohFbc X` the
restricted counit `Q(F)|_{U_étale} ⟶ F|_{U_étale}` is an isomorphism. -/
@[stacks 0GQK]
instance LQCohFbc.toQCoh_counit_restrictToSmallEtale_isIso
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (x : X.p.Fiber U) [AlgebraicStack.Flat (YonedaSlice.representative x)]
    (adj : QCoh.toLQCohFbc X ⊣ LQCohFbc.toQCoh X) (F : LQCohFbc X) :
    IsIso (LQCohFbc.toQCoh_counit_restrictToSmallEtale x adj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
