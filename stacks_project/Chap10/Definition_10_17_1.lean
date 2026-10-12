/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.17.1

The prime-spectrum objects and their `V`/`D` notation are owned by
`ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation`; this file keeps the three
source clauses as direct canonical recalls.

@stack 00DZ
-/

open PrimeSpectrum
open scoped PrimeSpectrum

/- Definition 10.17.1 (1): for a ring `R`, `Spec(R)` is the canonical type `PrimeSpectrum R` of
prime ideals of `R`. -/
@[stacks 00DZ "(1)"] #check @PrimeSpectrum

/- Definition 10.17.1 (2): for a subset `T ⊆ R`, the subset `V(T)` of `Spec(R)` is the canonical
zero locus `PrimeSpectrum.zeroLocus T`; the reusable notation and membership API are owned by
`PrimeSpectrum.mem_V`. -/
@[stacks 00DZ "(2)"] #check @zeroLocus
#check @mem_V

/- Definition 10.17.1 (3): for an element `f ∈ R`, the subset `D(f)` of `Spec(R)` is represented
by the canonical open `PrimeSpectrum.basicOpen f`, whose underlying set consists of the prime
ideals not containing `f`; the reusable notation and membership API are owned by
`PrimeSpectrum.mem_D`. -/
@[stacks 00DZ "(3)"] #check @basicOpen
#check @mem_D
