/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import stacks_project.Chap61.Lemma_61_25_1_Lift

/-!
# Geometric comparison for the affine ind-étale lift

The comparison `V ⟶ v(V)` is a closed immersion identifying `V` with the
fibre product `v(V) ×_X Z`. Every point of `v(V)` specializes to a point of
`V`, and `v` is cocontinuous and sends covering families to covering families.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- The comparison `V ⟶ v(V)` is a closed immersion. -/
instance AffineIndEtale.liftι_isClosedImmersion (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsClosedImmersion (AffineIndEtale.liftι i V) := sorry

/-- The comparison identifies `V` with the fibre product `v(V) ×_X Z`. -/
theorem AffineIndEtale.liftι_isPullback (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsPullback V.obj.hom (AffineIndEtale.liftι i V) i
      ((AffineIndEtale.lift i).obj V).obj.hom := sorry

/-- The adjunction unit identifies `V` with `u(v(V))`. -/
instance AffineIndEtale.lift_unit_isIso (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) :
    IsIso ((AffineIndEtale.liftAdjunction i).unit.app V) := sorry

/-- Every point of `v(V)` specializes to a point of `V`. -/
theorem AffineIndEtale.liftι_specializes (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z) (x : ((AffineIndEtale.lift i).obj V).obj.left) :
    ∃ y : V.obj.left, x ⤳ AffineIndEtale.liftι i V y := sorry

/-- Affine ind-étale lift is cocontinuous. -/
instance AffineIndEtale.lift_isCocontinuous (i : Z ⟶ X) [IsClosedImmersion i] :
    Functor.IsCocontinuous (AffineIndEtale.lift i)
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X) := sorry

/-- Affine ind-étale lift sends covering families to covering families. -/
theorem AffineIndEtale.lift_map_mem_precoverage (i : Z ⟶ X) [IsClosedImmersion i]
    {V : AffineIndEtale Z} {R : Presieve V}
    (hR : R ∈ affineIndEtalePrecoverage Z V) :
    R.map (AffineIndEtale.lift i) ∈
      affineIndEtalePrecoverage X ((AffineIndEtale.lift i).obj V) := sorry

/-- Topology-level covering preservation for affine ind-étale lift. -/
theorem AffineIndEtale.lift_coverPreserving (i : Z ⟶ X) [IsClosedImmersion i] :
    CoverPreserving (affineIndEtaleTopology Z) (affineIndEtaleTopology X)
      (AffineIndEtale.lift i) := sorry

end AlgebraicGeometry.Scheme.ProEt
