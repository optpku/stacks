/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap61.Lemma_61_25_1_Algebra
public import stacks_project.Chap61.Lemma_61_25_1_BaseChange
public import stacks_project.Chap61.Lemma_61_25_1_Lift
public import stacks_project.Chap61.Lemma_61_25_1_Comparison

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProEt

noncomputable section

universe u

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i]

/- Lemma 61.25.1 (1): the base change functor `u` sending `U` to `U ×_X Z` is
continuous on the affine ind-étale sites. -/
@[stacks 09BK] #check
  (AffineIndEtale.baseChange_isContinuous i :
    Functor.IsContinuous (AffineIndEtale.baseChange i)
      (affineIndEtaleTopology X) (affineIndEtaleTopology Z))

/- Lemma 61.25.1 (2): `u` has a fully faithful left adjoint `v`. -/
@[stacks 09BK] #check
  (AffineIndEtale.liftAdjunction i :
    AffineIndEtale.lift i ⊣ AffineIndEtale.baseChange i)

@[stacks 09BK] #check
  (AffineIndEtale.liftFullyFaithful i :
    (AffineIndEtale.lift i).FullyFaithful)

/- Lemma 61.25.1 (3): for `V` in the affine ind-étale site of `Z`, the morphism
`V ⟶ v(V)` is a closed immersion. -/
@[stacks 09BK] #check
  (AffineIndEtale.liftι_isClosedImmersion i :
    ∀ V : AffineIndEtale Z, IsClosedImmersion (AffineIndEtale.liftι i V))

/- Lemma 61.25.1 (4): the closed immersion identifies `V` with
`u(v(V)) = v(V) ×_X Z`. -/
@[stacks 09BK] #check
  (AffineIndEtale.lift_unit_isIso i :
    ∀ V : AffineIndEtale Z,
      IsIso ((AffineIndEtale.liftAdjunction i).unit.app V))

@[stacks 09BK] #check
  (AffineIndEtale.liftι_isPullback i :
    ∀ V : AffineIndEtale Z,
      IsPullback V.obj.hom (AffineIndEtale.liftι i V) i
        ((AffineIndEtale.lift i).obj V).obj.hom)

/- Lemma 61.25.1 (5): every point of `v(V)` specializes to a point of `V`. -/
@[stacks 09BK] #check
  (AffineIndEtale.liftι_specializes i :
    ∀ (V : AffineIndEtale Z) (x : ((AffineIndEtale.lift i).obj V).obj.left),
      ∃ y : V.obj.left, x ⤳ AffineIndEtale.liftι i V y)

/- Lemma 61.25.1 (6): the functor `v` is cocontinuous. -/
@[stacks 09BK] #check
  (AffineIndEtale.lift_isCocontinuous i :
    Functor.IsCocontinuous (AffineIndEtale.lift i)
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

/- Lemma 61.25.1 (7): the functor `v` sends covering families to covering
families. -/
@[stacks 09BK] #check
  (AffineIndEtale.lift_map_mem_precoverage i :
    ∀ {V : AffineIndEtale Z} {R : Presieve V},
      R ∈ affineIndEtalePrecoverage Z V →
        R.map (AffineIndEtale.lift i) ∈
          affineIndEtalePrecoverage X ((AffineIndEtale.lift i).obj V))
