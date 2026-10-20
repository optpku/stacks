/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.SectionsWithSupport.EtaleLocalization
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived`
-- pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `rightDerived`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.9.3: an étale morphism that is an isomorphism over a closed subspace preserves
all higher sheaves of sections with support and all cohomology groups with support.
The coefficient sheaf is on the target, as required by pullback and both source formulas. -/
@[stacks 0A4P] #check (AlgebraicGeometry.AlgebraicSpace.isIso_higherSectionsWithSupportEtaleBaseChangeHom :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {i : Z ⟶ Y}
    [Etale f] [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIso (higherSectionsWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q))

/- The comparison of cohomology groups uses global sections on the actual support. -/
#check (AlgebraicGeometry.AlgebraicSpace.isIso_cohomologyWithSupportEtaleBaseChangeHom :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {i : Z ⟶ Y}
    [Etale f] [IsClosedImmersion i] [IsIso (inverseImageTo f i)]
    (sectionsWithSupportY :
      Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjY : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupportY)
    (sectionsWithSupportX :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology (inverseImage f i)) AddCommGrpCat.{u + 1})
    (adjX : sheafPushforward AddCommGrpCat.{u + 1} (inverseImageι f i) ⊣ sectionsWithSupportX)
    [sectionsWithSupportY.Additive] [sectionsWithSupportX.Additive]
    (F : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ),
    IsIso (cohomologyWithSupportEtaleBaseChangeHom
      sectionsWithSupportY adjY sectionsWithSupportX adjX F q))
