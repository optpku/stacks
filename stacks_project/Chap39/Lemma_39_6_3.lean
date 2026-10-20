/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Group.Differentials
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonObj
open scoped AlgebraicGeometry

universe u

/- Lemma 39.6.3: Translation invariance identifies the relative differentials of a group
scheme with the pullbacks of its identity-section conormal sheaf and identity-restricted
differentials through canonical comparison morphisms. -/
@[stacks 047I] #check
  (AlgebraicGeometry.Scheme.GroupDifferentials.invariantDifferentialsComparison_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : Over S) [GrpObj G],
      IsIso (AlgebraicGeometry.Scheme.GroupDifferentials.translationComparison G) ∧
        IsIso
          (AlgebraicGeometry.Scheme.GroupDifferentials.conormalTranslationComparison G))

/- The pulled-back conormal comparison at the identity section is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.GroupDifferentials.conormalComparison_isIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : Over S) [GrpObj G],
      IsIso (AlgebraicGeometry.Scheme.GroupDifferentials.conormalComparison G))

/- Over the spectrum of a field, the relative differential sheaf of a group scheme is free. -/
#check
  (AlgebraicGeometry.Scheme.GroupDifferentials.differentials_isFree_of_field :
    ∀ {k : Type u} [Field k]
      (G : Over (AlgebraicGeometry.Spec (CommRingCat.of k))) [GrpObj G],
      SheafOfModules.IsFree Ω[G.hom.toShHom])
