module

public import ReasLib.RingTheory.MvPolynomial.Symmetric.FiniteFree
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.136.8 support index

The reusable elementary-symmetric map and finite-free result are owned directly by `ReasLib`.

@stack 00SR
-/

@[stacks 00SR "finite-free elementary-symmetric extension"]
#check @MvPolynomial.ElementarySymmetric.finiteFreeFin
