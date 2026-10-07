module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Model.Finite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.57.10

A finite module over a finite-type algebra admits a finite graded homogeneous-localization model.

@stack 052N
-/

/- Lemma 10.57.10 (Tag 052N): if `R'` is a finite-type `R`-algebra and `M` is a
finite `R'`-module, then there is an `ℕ`-graded algebra/module model with a degree-one
homogeneous element whose degree-zero away chart recovers `R'` and `M`; the algebra is generated
in degree one over degree zero and the graded module is finite. -/
@[stacks 052N]
#check @HomogeneousLocalization.Model.exists_of_finiteModule
