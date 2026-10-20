module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
import StacksCheckRecall

/-! # Pullback of module sheaves on algebraic spaces

@stack 03GA

The public owner uses the actual geometric and scalar constructions and preserves quasi-coherence.
-/

@[expose] public section

@[stacks 03GA "module pullback"]
#check @AlgebraicGeometry.AlgebraicSpace.Modules.pullback

@[stacks 03GA "preservation of quasi-coherence"]
#check @AlgebraicGeometry.AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty

#check @AlgebraicGeometry.AlgebraicSpace.QCoh.pullback
#check @AlgebraicGeometry.AlgebraicSpace.Modules.pullback_eq
#check @AlgebraicGeometry.AlgebraicSpace.structureMapScalarAdjunction
#check @AlgebraicGeometry.AlgebraicSpace.ringedToposHom
