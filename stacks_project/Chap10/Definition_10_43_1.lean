/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Nilpotent.GeometricallyReduced.TensorProduct
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Geometrically Reduced Algebras

Definition 10.43.1 is a canonical recall.  The ring-level owner is
`Algebra.IsGeometricallyReduced`; its field-base tensor criteria are owned by
`ReasLib.RingTheory.Nilpotent.GeometricallyReduced.TensorProduct`, while the affine-scheme
view lives in ReasLib.

@stack 030S
-/

/- Definition 10.43.1 (Tag 030S): the canonical notion of a geometrically reduced
`k`-algebra is `Algebra.IsGeometricallyReduced`. -/
@[stacks 030S]
#check @Algebra.IsGeometricallyReduced
@[stacks 030S "field characterization"]
#check @Algebra.isGeometricallyReduced_field_iff
@[stacks 030S "tensor-product characterization"]
#check @Algebra.IsGeometricallyReduced.iff_forall_isReduced_tensorProduct
@[stacks 030S "base-change preservation"]
#check @Algebra.IsGeometricallyReduced.baseChange
@[stacks 030S "base-change specialization"]
#check @Algebra.IsGeometricallyReduced.baseChange_of
@[stacks 030S "affine scheme bridge"]
#check @AlgebraicGeometry.SchemeOverField.geometricallyReduced_spec_iff_isGeometricallyReduced
