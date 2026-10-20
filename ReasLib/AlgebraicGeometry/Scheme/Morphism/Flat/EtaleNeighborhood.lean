/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type morphism that is flat at a point becomes flat and of finite
presentation on an open neighborhood of the unique point above it after an elementary
étale refinement and base change to the spectrum of the selected stalk. -/
theorem exists_elementaryEtale_flat_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (h_flat : f.flatAt x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let g := Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      ∃ x' : X',
        (Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
          ∃ V : X'.Opens, x' ∈ V ∧
            Flat (V.ι ≫ p) ∧ Scheme.Hom.FinitePresentation (V.ι ≫ p) := sorry

end AlgebraicGeometry.Scheme.Hom
