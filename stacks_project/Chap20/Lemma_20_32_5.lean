/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Preimage

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Module.Derived.Sections.Preimage

/-
Lemma 20.32.5: for `f : X ⟶ Y` and `V ⊆ Y`, derived sections on `f ⁻¹ᵁ V`, after restricting
scalars from `Γ(f ⁻¹ᵁ V, 𝒪_X)` to `Γ(V, 𝒪_Y)`, are canonically isomorphic to derived
pushforward followed by derived sections on `V`.

The reusable layer retains the concrete natural isomorphism between the canonical opens-site
models and supplies source-facing functor and objectwise views for the cochain-derived
ringed-space model.
-/

@[stacks 0D5W "Lemma 20.32.5: derived sections over inverse images and pushforward"]
#check @isomorphic

@[stacks 0D5W "derived inverse-image sections functor"]
#check @functor
@[stacks 0D5W "canonical inverse-image sections source"]
#check @canonicalSource
@[stacks 0D5W "canonical pushforward sections target"]
#check @canonicalTarget
@[stacks 0D5W "derived sections comparison isomorphism"]
#check @comparisonIso
@[stacks 0D5W "derived sections objectwise isomorphism"]
#check @obj_isomorphic
@[stacks 0D5W "derived global-sections pushforward isomorphism"]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.pushforwardIso

end
