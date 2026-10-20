/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.GlobalSections.TorIndependence
import StacksCheckRecall

/- Definition 36.22.2: let `S` be a scheme and let `X` and `Y` be schemes over `S`.
They are Tor independent over `S` if, for every `x ∈ X` and `y ∈ Y` mapping to the same
point `s ∈ S`, the stalk rings `𝒪_{X,x}` and `𝒪_{Y,y}` are Tor independent over
`𝒪_{S,s}`. -/
@[stacks 08IA] #check (@AlgebraicGeometry.Scheme.TorIndependentOver :
  {S : AlgebraicGeometry.Scheme} → CategoryTheory.Over S → CategoryTheory.Over S → Prop)
