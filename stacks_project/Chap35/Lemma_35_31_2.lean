/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.31.2: local finite-type quasi-finiteness of scheme morphisms is local on the
source for the étale precoverage. -/
@[stacks 03X4] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFiniteIsLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage)
