/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CartesianSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (C : InverseSystemCartesianSquare I)

/-- Pull back a bounded-below derived étale object on one stage along an inverse-system transition. -/
noncomputable def stagePlusPullback (i0 i : I) (hi : i0 ≤ i)
    (K0 : DerivedCategory.Plus
      (Sheaf (C.DT.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u + 1})) :
    DerivedCategory
      (Sheaf (C.DT.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (Derived.inverseImage (OrderDualInverseSystem.transitionMap C.DT hi)).obj
    (DerivedCategory.Plus.ι.obj K0)

/-- Pull back a bounded-below derived étale object on one stage along the limit-cone projection. -/
noncomputable def limitPlusPullback (i0 : I)
    (K0 : DerivedCategory.Plus
      (Sheaf (C.DT.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u + 1})) :
    DerivedCategory (Sheaf C.cT.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (Derived.inverseImage (C.cT.π.app (OrderDual.toDual i0))).obj
    (DerivedCategory.Plus.ι.obj K0)

/-- For an affine-transition inverse system of cartesian étale squares, isomorphic canonical
stagewise derived base-change maps imply that the canonical map for the limit square is an
isomorphism for every bounded-below coefficient pulled back from one stage. -/
theorem derivedBaseChange_of_inverseSystem_plus
    (C : InverseSystemCartesianSquare I)
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DX hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DY hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DS hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DT hij)]
    [∀ i : I, QuasiCompact (C.g i)]
    [∀ i : I, QuasiSeparated (C.g i)]
    [QuasiCompact C.gLim] [QuasiSeparated C.gLim]
    (i0 : I)
    (K0 : DerivedCategory.Plus
      (Sheaf (C.DT.obj (OrderDual.toDual i0)).smallEtaleTopology AddCommGrpCat.{u + 1}))
    (h_stage : ∀ (i : I) (hi : i0 ≤ i),
      IsIso (derivedMap (C.f i) (C.h i) (C.e i) (C.g i) (C.stage_isPullback i)
        (stagePlusPullback C i0 i hi K0))) :
    IsIso (derivedMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback
      (limitPlusPullback C i0 K0)) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
