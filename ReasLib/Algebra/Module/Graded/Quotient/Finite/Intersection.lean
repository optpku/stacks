/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
public import ReasLib.LinearAlgebra.Quotient.Intersection
import StacksCheckRecall

/-!
# Restricted quotient intersections in graded applications

For a graded family `𝒜`, the intersection and kernel attached to degree `i` are the specialization
of the general `Submodule.Quotient` API at `p := 𝒜 i`.  This file is a discoverability and Stacks-tag
facade only: it introduces no family-specific wrapper declarations and requires no `DecidableEq` or
decomposition instance.
-/

@[expose] public section

universe u v w x

variable {ι : Type u}
variable {R : Type v} [Ring R]
variable {S : Type w} [Ring S] [SMul R S]
variable {M : Type x} [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M]

/- Stacks `052N`: for one graded component, the ambient intersection with the quotient submodule
is canonically equivalent to the kernel of the quotient map restricted to that component.  The
family and index occur only in this specialization; neither belongs to the shared owner. -/
@[stacks 052N "restricted quotient component intersection infrastructure"] #check Submodule.Quotient.infEquivKer

/- The source-facing comap presentation remains a thin specialization of the ambient owner.  This
full type check protects the carrier orientation used by graded-submodule consumers. -/

/- The source-facing family is checked separately so this discoverability leaf cannot silently
forget the quotient grading while the generic owner remains free of grading parameters. -/
