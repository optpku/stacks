module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (L : X.Modules) [hL : Invertible L]

/- Definition 28.26.1: The invertible module `L` is ample when `X` is quasi-compact and, for
every `x : X`, there are `n : ℕ` with `0 < n` and a global section
`s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)` such that `x` belongs to the actual nonvanishing
open `hL.nonvanishingOpen s` and this open is affine. -/
@[stacks 01PS]
#check (AlgebraicGeometry.Scheme.Modules.IsAmple L : Prop)

end AlgebraicGeometry.Scheme.Modules
