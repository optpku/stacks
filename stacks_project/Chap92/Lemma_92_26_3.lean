/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.SchemeComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 92.26.3. For every morphism between schemes over a base scheme, the
cotangent complex of the represented algebraic-space morphism is canonically
identified with the genuine ε pullback of the scheme cotangent complex. -/
@[stacks 08VF] #check
  (AlgebraicGeometry.AlgebraicSpace.Cotangent.epsilonStarSchemeCompareIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0),
      AlgebraicGeometry.AlgebraicSpace.Cotangent.epsilonStarSchemeCotangent f0 ≅
        AlgebraicGeometry.AlgebraicSpace.Cotangent.cotangent
          (AlgebraicGeometry.AlgebraicSpace.ofOverMap f0))
