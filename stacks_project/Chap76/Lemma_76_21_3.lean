/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent.SchemeComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
universe u

/- Lemma 76.21.3. Let S be a scheme and let f : X ⟶ Y be a morphism of algebraic
spaces over S, represented by a scheme morphism f0 : X0 ⟶ Y0. There is a canonical
identification NL_{X/Y} ≅ ε* NL_{X0/Y0} in D(𝒪_X), where ε is the étale-to-Zariski
morphism and NL_{X0/Y0} is the scheme naive cotangent complex. -/
@[stacks 0D0X] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.ofOverHomIso_derived :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X0 Y0 : CategoryTheory.Over S}
      (f0 : X0 ⟶ Y0),
      DerivedCategory.Q.obj
          (AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent.epsilonStarComplex f0) ≅
        DerivedCategory.Q.obj
          (AlgebraicGeometry.AlgebraicSpace.Hom.naiveCotangent
            (AlgebraicGeometry.AlgebraicSpace.ofOverMap f0)))
