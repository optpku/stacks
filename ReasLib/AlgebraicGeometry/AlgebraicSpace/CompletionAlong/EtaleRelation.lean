/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale

/-!
# Étale equivalence relations from open complements and completions

A pair of morphisms that forms an étale equivalence relation over an open
complement and an internal equivalence relation with étale projections after
completion extends to an étale equivalence relation globally.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

set_option synthInstance.checkSynthOrder false in
/-- A pair of morphisms locally of finite type over a locally Noetherian
algebraic space forms an étale equivalence relation if it does so over the
complement of a closed subset and forms an internal equivalence relation with
étale projections after completion along that subset. -/
instance isEtaleEquivalenceRelation {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {R U : Over X} (t s : R ⟶ U)
    [LocallyOfFiniteType R.hom] [LocallyOfFiniteType U.hom]
    [IsEtaleEquivalenceRelation ((overPullback (openComplementι X T)).map t)
      ((overPullback (openComplementι X T)).map s)]
    [IsEquivalenceRelation (mapOver T t) (mapOver T s)]
    [FormalAlgebraicSpace.Etale (mapOver T t)]
    [FormalAlgebraicSpace.Etale (mapOver T s)] :
    IsEtaleEquivalenceRelation t s :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
