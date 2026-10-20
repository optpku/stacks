module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ContinuousMap
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf TopCat TopCat.Presheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf CommRingCat.{u})

/- Lemma 6.24.4: morphisms from `𝒪 ⊗_{c_𝒪} f_p 𝒢` to `ℱ` correspond canonically to
morphisms from `𝒢` to the direct image of `ℱ`, with its induced `f_*𝒪`-module structure.
The textbook tensor notation is the source-facing presentation of the neutral
`TopCat.Presheaf.modulePullback` construction. -/
@[stacks 008V]
#check TopCat.Presheaf.modulePullbackHomEquiv (f := f) (𝒪 := 𝒪)

end
