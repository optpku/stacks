module

public import ReasLib.Topology.Specialization.Dimension.Obstruction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe w u

variable (X : Type u) [TopologicalSpace X]
  [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/- Remark 5.20.5: the obstruction to a global dimension function is a class
in degree-one cohomology of the constant sheaf `ℤ`. -/
@[stacks 02ID]
#check (CatenarySpace.dimensionFunctionObstruction X :
  (locallyConstantSheaf X ℤ).H 1)

@[stacks 02ID]
#check (CatenarySpace.dimensionFunctionObstruction_eq_zero_iff (X := X) :
  CatenarySpace.dimensionFunctionObstruction X = 0 ↔
    ∃ δ : X → ℤ, IsDimensionFunction δ)
