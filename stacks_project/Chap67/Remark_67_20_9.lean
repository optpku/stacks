/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 67.20.9: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, `f` factors canonically as
`X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) ⟶ Y`. -/
@[stacks 081X] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toPushforwardRelativeSpec_comp_relativeSpecπ :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      Hom.toPushforwardRelativeSpec f ≫
          relativeSpecπ (pushforwardStructureQcAlgebra f) =
        f)
