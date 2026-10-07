module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}
variable (hpb : IsPullback f h' h g) (p : ℕ)

/- Lemma 50.2.1: for a cartesian square of schemes, the canonical map
`f^* Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` is an isomorphism. -/
@[stacks 0FL5] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.formComparison_isIso_of_isPullback hpb p :
    IsIso (AlgebraicGeometry.Scheme.RelativeDifferentials.formComparison hpb.toCommSq p))

end AlgebraicGeometry.Scheme.RelativeDifferentials
