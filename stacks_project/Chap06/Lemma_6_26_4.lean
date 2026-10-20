module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.PullbackStalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable (𝒢 : Y.Modules) (x : X)

/- Lemma 6.26.4: the canonical comparison
`𝒢_{f(x)} ⊗[𝒪_{Y,f(x)}] 𝒪_{X,x} ⟶ (f^*𝒢)_x` is an isomorphism of
`𝒪_{X,x}`-modules. -/
@[stacks 0098]
#check pullbackStalkIso f 𝒢 x

end AlgebraicGeometry.RingedSpace.Hom
