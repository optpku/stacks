module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.71.2 Compatibility Facade

The reusable owners for termwise free and finite conditions, free resolutions, finite free
resolutions, and their projective-resolution comparison are now
`ReasLib.Algebra.Homology.HomologicalComplex.Termwise` and
`ReasLib.Algebra.Homology.ChainComplex.FreeResolution`.  This historical import path remains
available to Chapter 10 and downstream developments.

@stack 00LQ
-/

/- Definition 10.71.2 (1): a resolution of a module is a quasi-isomorphism from a chain complex
to the complex concentrated in degree zero. -/
@[stacks 00LQ "(1)"]
#check @QuasiIso

/- Definition 10.71.2 (2): a free resolution is a resolution whose terms are free modules. -/
@[stacks 00LQ "(2)"]
#check @ChainComplex.IsFreeResolution

/- Definition 10.71.2 (3): a finite free resolution is a free resolution whose terms are finite
modules. -/
@[stacks 00LQ "(3)"]
#check @ChainComplex.IsFiniteFreeResolution

@[stacks 00LQ "degree-zero module complex"]
#check @ChainComplex.moduleSingle
@[stacks 00LQ "free-resolution characterization"]
#check @ChainComplex.isFreeResolution_iff
@[stacks 00LQ "finite free-resolution characterization"]
#check @ChainComplex.isFiniteFreeResolution_iff
@[stacks 00LQ "projective-resolution bridge"]
#check @ChainComplex.IsFreeResolution.toProjectiveResolution
