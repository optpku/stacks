/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.SchemeComparison

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

/- Lemma 71.10.5: for a scheme representing an algebraic space whose weakly associated
points have codimension zero and which has finitely many irreducible components on compact
opens, the meromorphic-function algebra agrees with the associated Zariski algebra. -/
@[stacks 0EN7] #check
  (AlgebraicGeometry.AlgebraicSpace.meromorphicFunctionSheaf_isIsomorphic_associated :
    ∀ {S : Scheme.{u}} (T : Over S)
      [HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)]
      (hweak : (ofOver T).weakAss ⊆ codimZeroPoints (ofOver T)),
      IsIsomorphic (Under.mk (toMeromorphicFunctionSheafHom (ofOver T)))
        (Under.mk (associatedToMeromorphicFunctionSheafHom T)))

#check (AlgebraicGeometry.AlgebraicSpace.associatedMeromorphicFunctionSheaf_isQuasicoherent :
  ∀ {S : Scheme.{u}} (T : Over S)
    [HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)]
    (hweak : (ofOver T).weakAss ⊆ codimZeroPoints (ofOver T)),
    ((restrictionAlong (associatedToMeromorphicFunctionSheafHom T)).obj
      (unitModule (smallEtaleTopology (ofOver T))
        (associatedMeromorphicFunctionSheaf T))).IsQuasicoherent)
