module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Free
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

/-!
# Lemma 10.13.1

@stack 00DN
-/

/- Lemma 10.13.1 (1) [stacks 00DN]: for a free `R`-module, the canonical ReasLib instance
`SymmetricPower.instFreeFin` supplies freeness of the standard finite symmetric power
`Sym[R]^n M`. The universe-polymorphic owner is `SymmetricPower.instFree` on `UFin n`. -/
@[stacks 00DN "symmetric powers of free modules"]
#check @SymmetricPower.instFreeFin

/- Lemma 10.13.1 (2): for a free `R`-module, the canonical mathlib instance
`exteriorPower.instFree` supplies freeness of `⋀[R]^n M`. -/
@[stacks 00DN "exterior powers of free modules"]
#check @exteriorPower.instFree
