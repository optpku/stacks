/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints

@[expose] public section

namespace AlgebraicGeometry.Scheme

open TopologicalSpace

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- For an open subscheme of a locally Noetherian scheme, scheme-theoretic density is
equivalent both to topological density together with containment of all embedded points and
to containment of all associated points. -/
theorem schemeTheoreticallyDense_open_tfae_dense_embeddedPoints_associatedPoints
    (U : X.Opens) :
    List.TFAE [
      schemeTheoreticallyDense U,
      Dense (U : Set X) ∧ X.embeddedPoints ⊆ (U : Set X),
      X.associatedPoints ⊆ (U : Set X)
    ] := sorry

end AlgebraicGeometry.Scheme
