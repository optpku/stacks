module

public import stacks_project.Chap73.Definition_73_4_1_Precoverage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}}

/- Definition 73.4.1 -/
@[stacks 041E] #check (etalePrecoverage : Precoverage (AlgebraicSpace S))

#check ofArrows_mem_etalePrecoverage_iff
