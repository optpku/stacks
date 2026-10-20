/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.CodimensionZero

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

universe u

/- Lemma 71.10.8. Meromorphic functions and quasi-coherent meromorphic sections are both
coproducts and products of canonical codimension-zero stalk direct images, and rational
functions are global meromorphic functions. -/
@[stacks 0ENA] #check (AlgebraicGeometry.AlgebraicSpace.meromorphic_codimZero_decomposition :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η),
    ∃ c : codimZeroPoints X → OpenImmersionChart X,
      (∀ η, Points.mapOfOver (c η).ι (c η).u = η) ∧
      IsIsomorphic (meromorphicFunctionSheaf X) (codimZeroStalkPushforwardProductSheaf c) ∧
      IsIsomorphic (meromorphicFunctionModule X)
        (codimZeroStalkPushforwardCoproductModule c (SheafOfModules.unit (structureSheaf X))) ∧
      IsIsomorphic
        (codimZeroStalkPushforwardCoproductModule c (SheafOfModules.unit (structureSheaf X)))
        (codimZeroStalkPushforwardProductModule c (SheafOfModules.unit (structureSheaf X))) ∧
      (∀ (F : X.Modules) [F.IsQuasicoherent],
        IsIsomorphic
          ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
            (meromorphicSectionSheaf X F))
          (codimZeroStalkPushforwardCoproductModule c F) ∧
        IsIsomorphic (codimZeroStalkPushforwardCoproductModule c F)
          (codimZeroStalkPushforwardProductModule c F)) ∧
      IsIsomorphic (rationalFunctionRing X) (meromorphicFunctions X))
