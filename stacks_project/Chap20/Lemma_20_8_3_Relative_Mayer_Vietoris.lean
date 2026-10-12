/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.RelativeMayerVietoris
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace.Module.Cohomology.RelativeMayerVietoris

/- Lemma 20.8.3 (01EC): relative Mayer--Vietoris exactness for a morphism of ringed spaces. -/
@[stacks 01EC "initial relative Mayer--Vietoris exact segment"]
#check @existsInitial

/- The source's boundary-existence clause is exposed separately for reuse. -/
@[stacks 01EC "relative Mayer--Vietoris exact segment"]
#check @existsExact

@[stacks 01EC "relative Mayer--Vietoris middle exactness"]
#check @middleExact

#check @comp_zero
#check @shortComplex
#check @leftMono
#check @AlgebraicGeometry.RingedSpace.Module.Cohomology.RelativeMayerVietoris.sequence
