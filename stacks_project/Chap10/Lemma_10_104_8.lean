module

public import ReasLib.RingTheory.Depth.CohenMacaulay.FiniteFreePresentation
import StacksCheckRecall

/-!
# Depth in a finite-free presentation

@stack 00NE
-/

/- Lemma 10.104.8: a finite-free presentation over a Cohen--Macaulay local ring
has the depth trichotomy recorded by the intrinsic short-exact owner. -/
@[stacks 00NE]
#check @CategoryTheory.ShortComplex.ShortExact.moduleDepth_kernel_trichotomy_of_finiteFree
