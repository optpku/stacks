module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Section
import StacksCheckRecall

/-! # Regular sections

The canonical section map and regularity predicate are owned by the public module.
Stacks 0843 is its invertible-module specialization.
-/

@[expose] public section

@[stacks 0843] #check @AlgebraicGeometry.AlgebraicSpace.IsRegularSection
#check @AlgebraicGeometry.AlgebraicSpace.regularSectionHom
#check @AlgebraicGeometry.AlgebraicSpace.unitHomEquiv_regularSectionHom
#check @AlgebraicGeometry.AlgebraicSpace.isRegularSection_iff_mono
#check @AlgebraicGeometry.AlgebraicSpace.instIsRegularSection_unit
