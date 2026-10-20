/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived
open scoped AlgebraicGeometry

noncomputable section

universe u

/- 43.22.1.1: if the restriction of a flat proper morphism to `V` is finite near
`ξ`, then the stalk at `ξ` of the pushforward of
`Tor i 𝒪V (pullback f 𝒪W)` is isomorphic to the stalk of
`Tor i (pushforward f 𝒪V) 𝒪W`. -/
@[stacks 0B11] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.stalkPushforwardTor_isomorphic :
    ∀ {k : Type u} [Field k]
      (X Y : SchemeOverField k) [Variety X] [Variety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
      [Tensor.Has X.left.toRingedSpace]
      [Tensor.Has Y.left.toRingedSpace]
      (V : X.left.IdealSheafData) (W : Y.left.IdealSheafData)
      [Variety (Over.mk (V.subschemeι ≫ X.hom))]
      [Variety (Over.mk (W.subschemeι ≫ Y.hom))]
      (ξ : Y.left)
      (hfinite : ∃ U : Y.left.Opens, ξ ∈ U ∧
        IsFinite ((V.subschemeι ≫ f.left) ∣_ U)) (i : ℕ),
      let 𝒪V : X.left.Modules :=
        (Scheme.Modules.pushforward V.subschemeι).obj
          (SheafOfModules.unit V.subscheme.ringCatSheaf : V.subscheme.Modules)
      let 𝒪W : Y.left.Modules :=
        (Scheme.Modules.pushforward W.subschemeι).obj
          (SheafOfModules.unit W.subscheme.ringCatSheaf : W.subscheme.Modules)
      IsIsomorphic
        (RingedSpace.stalkModuleCat
          ((Scheme.Modules.pushforward f.left).obj
            (RingedSpace.ModuleDerived.tor i 𝒪V
              ((Scheme.Modules.pullback f.left).obj 𝒪W))) ξ)
        (RingedSpace.stalkModuleCat
          (RingedSpace.ModuleDerived.tor i
            ((Scheme.Modules.pushforward f.left).obj 𝒪V) 𝒪W) ξ))
