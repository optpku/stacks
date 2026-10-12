/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First cotangent homology under flat source change

This leaf records the canonical invariance of first cotangent homology when
the source algebra is changed along a flat map.
-/

@[expose] public section

universe u v w

namespace Algebra.H1Cotangent

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Tag `00S4`: flat change of the source algebra induces a bijective
canonical map on first cotangent homology.  Flatness is an explicit
proposition so one-off base-change arguments need not install a local
instance. -/
@[stacks 00S4 "flat source change on first cotangent homology"]
theorem map_bijective_of_flat
    (hflat : Module.Flat R S) :
    Function.Bijective (map R S T T) := sorry

end Algebra.H1Cotangent
