module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf TopCat

noncomputable section

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
variable (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X)

/- Lemma 6.14.2 (Tag 007K): the canonical comparison
`ℱ_x ⊗[𝒪_x] 𝒪'_x ⟶ (ℱ ⊗_{p, 𝒪} 𝒪')_x` is an isomorphism. -/
@[stacks 007K]
#check stalkBaseChangeComparisonIso p ℱ x

end TopCat.Presheaf
