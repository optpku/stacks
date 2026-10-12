/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k] [PerfectField k]

namespace SchemeOverField

namespace RegularLocus

/-- Over a perfect field, a point of a reduced locally algebraic scheme is smooth over the
field if and only if it lies in the regular locus. -/
theorem smoothAt_iff
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left]
    (x : X.left) : X.hom.SmoothAt x ↔ x ∈ Reg(X.left) := sorry

/-- Over a perfect field, the smooth locus of a reduced locally algebraic scheme equals its
regular locus. -/
theorem smoothAt_set_eq
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left] :
    { x : X.left | X.hom.SmoothAt x } = Reg(X.left) := sorry

/-- The regular locus of a reduced locally algebraic scheme over a perfect field is open. -/
theorem isOpen
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left] :
    IsOpen (Reg(X.left) : Set X.left) := sorry

/-- The regular locus of a reduced locally algebraic scheme over a perfect field is dense. -/
theorem dense
    (X : Over (Spec (CommRingCat.of k))) [LocallyAlgebraic X] [IsReduced X.left] :
    Dense (Reg(X.left) : Set X.left) := sorry

end RegularLocus

end SchemeOverField

end

end AlgebraicGeometry
