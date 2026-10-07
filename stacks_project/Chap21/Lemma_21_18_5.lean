module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.MixedTensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.18.5

The reusable owner factors pullback through modules over `f⁻¹𝒪_Y` and models the mixed derived
tensor product by derived extension of scalars followed by the ambient tensor product over
`𝒪_X`.  The chapter entry only recalls the canonical comparison and its isomorphism views.
-/

/- Lemma 21.18.5 (08I6): for `F ∈ D(𝒪_X)` and `G ∈ D(𝒪_Y)`, the canonical comparison
identifies `F ⊗ᴸ_[𝒪_X] Lf⁎G` with the mixed derived tensor product
`F ⊗ᴸ_[f⁻¹𝒪_Y] f⁻¹G`. -/
@[stacks 08I6 "canonical mixed derived tensor comparison"]
#check @RingedSite.Hom.modulePullbackDerived.MixedTensor.compComparison_isIso

#check @RingedSite.Hom.modulePullbackDerived.MixedTensor.natIso
#check @RingedSite.Hom.modulePullbackDerived.MixedTensor.iso
#check @RingedSite.Hom.PullbackFactorization.hom_eq
