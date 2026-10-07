module

public import stacks_project.Chap91.Situation_91_6_2_Diagram
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

universe u

/- Definition 91.3.2: In Situation 91.3.1, a morphism of thickenings `(f, f')`
is strict when the comparison `(f')^* 𝒥 ⟶ ℐ` is a surjective map of
`𝒪_{X'}`-modules. -/
@[stacks 08L1] #check (Thickening.Hom.IsStrict : {T U : Thickening.{u}} → (T ⟶ U) → Prop)

/- Surjectivity of `(f')^* 𝒥 ⟶ ℐ` is epimorphicity of `Hom.idealMap`. -/
#check Thickening.Hom.isStrict_iff
