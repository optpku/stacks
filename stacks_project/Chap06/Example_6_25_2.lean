module

public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
public import ReasLib.Topology.Sheaves.ContinuousFunctions.Real
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

/- Example 6.25.2 (1): a continuous map `f : X ⟶ Y` induces the canonical morphism
`𝒞⁰_Y ⟶ f_*𝒞⁰_X` of sheaves of `ℝ`-algebras. -/
@[stacks 0092 "continuous pullback on real-valued functions"]
#check TopCat.ContinuousFunctions.pushforwardMap ℝ

/- Example 6.25.2 (2): on an open subset `V ⊆ Y`, the induced morphism sends
`h : V → ℝ` to `h ∘ f|_{f ⁻¹' V}`. -/
@[stacks 0092 "sectionwise formula for continuous pullback"]
#check TopCat.ContinuousFunctions.pushforwardMap_app ℝ

/- Mathlib packages the source's smooth-manifold analogue at the stronger locally ringed-space
layer: its structure sheaf is the sheaf of smooth scalar-valued functions, and the underlying sheaf
map is precomposition by the smooth map. A direct recall avoids a duplicate manifold-specific
wrapper while retaining the source's canonical morphism. -/
/- Example 6.25.2 (3): an infinitely differentiable map of smooth manifolds induces the canonical
morphism of locally ringed spaces defined by pullback of smooth functions. -/
@[stacks 0092 "smooth maps induce locally ringed-space morphisms"]
recall ChartedSpace.locallyRingedSpaceMap
