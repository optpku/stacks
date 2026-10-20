/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ClosedImmersion
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 61.25.3 (1): if `i : Z ⟶ X` is a closed immersion of schemes, then
the small pro-étale inverse image `(smallProetalePullback i).sheafPullback`
preserves limits of Type-valued sheaves. -/
@[stacks 09AA] #check
  (AlgebraicGeometry.Scheme.ProEt.inverseImage_preservesLimits_of_isClosedImmersion :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      PreservesLimits ((smallProetalePullback i).sheafPullback (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)))

/- Lemma 61.25.3 (2): if `i : Z ⟶ X` is a closed immersion of schemes, then
the small pro-étale direct image
`(smallProetalePullback i).sheafPushforwardContinuous` is fully faithful on
Type-valued sheaves. -/
@[stacks 09AA] #check
  (AlgebraicGeometry.Scheme.ProEt.pushforwardFullyFaithful_of_isClosedImmersion :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      ((smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).FullyFaithful)

/- Lemma 61.25.3 (3): if `i : Z ⟶ X` is a closed immersion of schemes, then
the adjunction counit identifies direct image followed by inverse image with
the identity on Type-valued sheaves on the small pro-étale topos of `Z`. -/
@[stacks 09AA] #check
  (AlgebraicGeometry.Scheme.ProEt.sheafAdjunction_counit_isIso_of_isClosedImmersion :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [HasSheafify (ProEt.topology X) (Type (u + 1))]
      [HasSheafify (ProEt.topology Z) (Type (u + 1))],
      IsIso ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
        (ProEt.topology X) (ProEt.topology Z)).counit)
