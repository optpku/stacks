/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionsWithSupport
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.9.2: for a closed immersion `i : Z ⟶ X` of algebraic spaces over a scheme `S`
and an injective abelian sheaf `G` on the small étale site of `Z`, one has
`ℋ^p_Z((sheafPushforward i).obj G) = 0` for `p > 0`. -/
@[stacks 0A4N] #check
  (AlgebraicGeometry.AlgebraicSpace.closedImmersion_higherSectionsWithSupport_isZero :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjunction : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})]
    [sectionsWithSupport.Additive]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1}) [Injective G]
    (p : ℕ) (hp : 0 < p),
    IsZero ((sectionsWithSupport.rightDerived p).obj
      ((sheafPushforward AddCommGrpCat.{u + 1} i).obj G)))
