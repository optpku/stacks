/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Étale base change and reductions of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]

/-- Base change of an étale morphism along an algebraic-space valued map,
with its actual presheaf pullback as functor of points. -/
def etalePullback (f : X ⟶ Y) [hf : Etale f] (T : AlgebraicSpace S)
    (g : T.functorOfPoints ⟶ Y) : AlgebraicSpace S :=
  let h := @AlgebraicSpace.IsAlgebraicSpace.pullback S X Y T.functorOfPoints
    f hf.representable (AlgebraicSpace.instIsAlgebraicSpace_functorOfPoints T) g
  AlgebraicSpace.ofFunctor (pullback g f) h.isSheaf h.representableDiagonal h.atlas

/-- The projection from an étale base change to its algebraic-space base. -/
def etalePullbackProjection (f : X ⟶ Y) [Etale f] (T : AlgebraicSpace S)
    (g : T.functorOfPoints ⟶ Y) : etalePullback f T g ⟶ T :=
  pullback.fst g f

/-- Base change of an étale morphism to an algebraic space is étale. -/
theorem etalePullback_etale (f : X ⟶ Y) [Etale f] (T : AlgebraicSpace S)
    (g : T.functorOfPoints ⟶ Y) :
    AlgebraicSpace.Etale (etalePullbackProjection f T g) :=
  sorry

/-- An étale base change over a reduced algebraic space is reduced. -/
theorem etalePullback_isReduced (f : X ⟶ Y) [Etale f] (T : AlgebraicSpace S)
    (g : T.functorOfPoints ⟶ Y)
    (hT : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) T) :
    AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) (etalePullback f T g) :=
  sorry

/-- The reduction square of an étale morphism of formal algebraic spaces is cartesian. -/
theorem ReductionData.map_isPullback (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    IsPullback RX.ι (ReductionData.map RX RY f) f RY.ι :=
  sorry

/-- An étale morphism of formal algebraic spaces induces an étale morphism of reductions. -/
theorem ReductionData.map_etale (RX : ReductionData X) (RY : ReductionData Y)
    (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.Etale (ReductionData.map RX RY f) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
