module

public import ReasLib.NumberTheory.Padics.PrimeTo.Basic

/-!
# Prime-to-q adic integer data for Example 64.30.2

The product, its specified Chinese remainder reductions and its canonical unit are owned by
`ReasLib.NumberTheory.Padics.PrimeTo.Basic`. The source examples continue to use those exact data.
-/

@[expose] public section

#check PadicInt.PrimeTo
#check PadicInt.PrimeTo.toZMod
#check PadicInt.PrimeTo.natCastUnit
#check PadicInt.PrimeTo.trivialModuleCongruence
