module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
import StacksCheckRecall

/-! # Kernel ideal sheaf of a closed immersion

@stack 03MB

The actual public kernel map and subobject retain the source ideal sheaf.
-/

@[expose] public section

@[stacks 03MB "kernel ideal sheaf"]
#check @AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafSubobject

@[stacks 03MB "quasi-coherence"]
#check @AlgebraicGeometry.AlgebraicSpace.Hom.instIsQuasiCoherent_idealSheafSubobject

#check @AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafMap
#check @AlgebraicGeometry.AlgebraicSpace.Hom.idealSheaf
#check @AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafι
#check @AlgebraicGeometry.AlgebraicSpace.Hom.idealSheaf_spec
