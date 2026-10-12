/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 41.3.5 (1): for a locally finite-type morphism to a locally Noetherian
scheme, unramifiedness at a point is equivalent to the maximal-ideal and finite separable
residue-field criterion for the induced local-ring map. -/
@[stacks 024N] #check
  (AlgebraicGeometry.Scheme.Hom.unramifiedAt_iff_localRingCriterion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
      (x : X),
      f.UnramifiedAt x ↔ MaximalIdealResidueFieldUnramifiedAtCriterion f x)

/- Definition 41.3.5 (2): a locally finite-type morphism to a locally Noetherian scheme is
unramified exactly when the local-ring criterion holds at every source point. -/
@[stacks 024N] #check
  (AlgebraicGeometry.Scheme.Hom.unramified_iff_forall_localRingCriterion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f],
      Unramified f ↔ ∀ x : X, MaximalIdealResidueFieldUnramifiedAtCriterion f x)

end AlgebraicGeometry.Scheme.Hom
