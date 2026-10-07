module

public import stacks_project.Chap91.Situation_91_9_1_Comparison
public import stacks_project.Chap91.Situation_91_9_1_Thickening
import StacksCheckRecall

open RingedSite.ToposHom

/- Situation 91.9.1 (1): a morphism of thickenings of ringed topoi `(f, f')` is a
commutative diagram of ringed topoi whose horizontal arrows are thickenings. -/
@[stacks 08M7] #check Thickening.homMk

/- Situation 91.9.1 (2): set ℐ = Ker(i^♯) ⊂ 𝒪' and 𝒥 = Ker(t^♯) ⊂ 𝒪_{B'}.
Then `(f')^♯` induces the 𝒪'-module map `(f')^* 𝒥 ⟶ ℐ`. -/
@[stacks 08M7] #check Thickening.idealMap

/- Situation 91.9.1 (3): if i and t are first-order thickenings, then
`(f')^* 𝒥 = f^* 𝒥` and the map above becomes an 𝒪-module map `f^* 𝒥 ⟶ ℐ`. -/
@[stacks 08M7] #check Thickening.sourceIdealMap
