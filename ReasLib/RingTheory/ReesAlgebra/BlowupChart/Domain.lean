/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart

/-!
# Domain structure on affine blowup charts

This leaf owns the generic permanence statement that an affine blowup chart of a
domain is again a domain when its chart parameter is nonzero.  The statement is
kept separate from the chart construction so downstream users can import the
property without importing chapter-facing wrappers.
-/

@[expose] public section

universe u

namespace AffineBlowupChart

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A nonzero-parameter affine blowup chart of a domain is a domain. -/
@[stacks 052R "domain affine blowup chart"]
instance instIsDomain (I : Ideal R) (a : I) [Fact ((a : R) ≠ 0)] :
    IsDomain (affineBlowupChart I a) := sorry

/-- A chart indexed by an explicitly nonzero parameter also inherits the domain instance.

This bridge keeps subtype-indexed APIs, such as fraction-field maps, from rebuilding a local
`Fact` instance at every use site. -/
@[stacks 052R "domain chart from an explicit nonzero parameter"]
instance instIsDomainOfNonzero
    (I : Ideal R) (a : NonzeroParameter I) :
    IsDomain (affineBlowupChart I a) := sorry

end AffineBlowupChart
