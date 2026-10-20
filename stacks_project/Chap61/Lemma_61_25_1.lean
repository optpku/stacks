/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleClosedImmersion

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
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.baseChange_isContinuous i :
    Functor.IsContinuous (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.baseChange i)
      (affineIndEtaleTopology X) (affineIndEtaleTopology Z))

/- Lemma 61.25.1 (2): `u` has a fully faithful left adjoint `v`. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftAdjunction i :
    AffineIndEtale.lift i ⊣ AffineIndEtale.baseChange i)

/- Lemma 61.25.1 (2): full faithfulness of the constructed left adjoint. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftFullyFaithful i :
    (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i).FullyFaithful)

/- Lemma 61.25.1 (3): for `V` in the affine ind-étale site of `Z`, the morphism
`V ⟶ v(V)` is a closed immersion. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftι_isClosedImmersion i :
    ∀ V : AffineIndEtale Z, IsClosedImmersion (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftι i V))

/- Lemma 61.25.1 (4): the closed immersion identifies `V` with
`u(v(V)) = v(V) ×_X Z`. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift_unit_isIso i :
    ∀ V : AffineIndEtale Z,
      IsIso ((AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftAdjunction i).unit.app V))

/- Lemma 61.25.1 (4): the comparison square is a pullback. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftι_isPullback i :
    ∀ V : AffineIndEtale Z,
      IsPullback V.obj.hom (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftι i V) i
        ((AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i).obj V).obj.hom)

/- Lemma 61.25.1 (5): every point of `v(V)` specializes to a point of `V`. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.liftι_specializes i :
    ∀ (V : AffineIndEtale Z) (x : ((AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i).obj V).obj.left),
      ∃ y : V.obj.left, x ⤳ AffineIndEtale.liftι i V y)

/- Lemma 61.25.1 (6): the functor `v` is cocontinuous. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift_isCocontinuous i :
    Functor.IsCocontinuous (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i)
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

/- Lemma 61.25.1 (7): the functor `v` sends covering families to covering
families. -/
@[stacks 09BK] #check
  (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift_map_mem_precoverage i :
    ∀ {V : AffineIndEtale Z} {R : Presieve V},
      R ∈ affineIndEtalePrecoverage Z V →
        R.map (AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i) ∈
          affineIndEtalePrecoverage X ((AlgebraicGeometry.Scheme.ProEt.AffineIndEtale.lift i).obj V))
