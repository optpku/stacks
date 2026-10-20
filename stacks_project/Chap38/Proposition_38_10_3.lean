/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 38.10.3: a finite-type quasicoherent module that is flat at `x` over a
locally finitely presented morphism becomes finitely presented and flat on an open
neighborhood of the unique point over `x`, after an elementary étale refinement followed
by base change to the spectrum of the selected stalk. -/
@[stacks 05I5] #check
  (AlgebraicGeometry.Scheme.Modules.exists_elementaryEtale_finitePresentation_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (x : X) (h_flat : AlgebraicGeometry.Scheme.Modules.flatOverAt F f x),
      ∃ U : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary S (f x),
        let E := U.obj
        let g := AlgebraicGeometry.Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
        let X' := CategoryTheory.Limits.pullback f g
        let p := CategoryTheory.Limits.pullback.snd f g
        let F' := AlgebraicGeometry.Scheme.Modules.baseChangeModule f g F
        ∃ x' : X',
          (CategoryTheory.Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
            ∃ V : X'.Opens, x' ∈ V ∧
              (F'.restrict V.ι).IsFinitePresentation ∧
                AlgebraicGeometry.Scheme.Modules.flatOver (F'.restrict V.ι) (V.ι ≫ p))
