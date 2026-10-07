module

public import stacks_project.Chap91.Definition_91_9_2_Strict
import StacksCheckRecall

open RingedSite.ToposHom

/- Definition 91.9.2: In Situation 91.9.1, a morphism of thickenings `(f, f')`
is strict when the comparison `(f')^* 𝒥 ⟶ ℐ` is a surjective map of
`𝒪'`-modules. -/
@[stacks 08M9] #check Thickening.IsStrict

/- Surjectivity of `(f')^* 𝒥 ⟶ ℐ` is epimorphicity of `idealMap`. -/
#check Thickening.isStrict_iff
