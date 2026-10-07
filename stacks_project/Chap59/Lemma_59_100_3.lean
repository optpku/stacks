module

public import stacks_project.Chap59.Lemma_59_100_3_Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace SmallToBig

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Lemma 59.100.3: in the commuting topos square of Lemma 59.100.2, if `f : X ⟶ Y` is
proper, then the canonical mate `fppfSmallPushforwardHom f` from
`(smallMorphism f).pushforward ⋙ (fppfComparison Y)⁻¹` to
`(fppfComparison X)⁻¹ ⋙ (Fppf.Big.morphismOfTopoi f).pushforward` is an isomorphism
of functors on sheaves of sets. Here `fppfComparison S` is the composite
`a_S = π_S ∘ ε_S` of `siteMorphismOfTopoi S` with `StandardTopology.toFppf .etale S`,
so the mate is the comparison `a_Y⁻¹ ∘ f_small,* ⟶ f_big,fppf,* ∘ a_X⁻¹`. -/
@[stacks 0DDN]
theorem proper_fppfSmallPushforward_isIso [IsProper f] :
    IsIso (fppfSmallPushforwardHom f) := sorry

end SmallToBig
end AlgebraicGeometry.Scheme.Etale

end

end
