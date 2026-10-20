/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Affine
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Basic big syntomic slice API

This leaf owns the topology-specific categorical data attached to a morphism of
schemes on the big syntomic slice sites.  Sheaf-level constructions are kept in
`Sites.Syntomic.Big` so applications that only need the slice adjunction do not
pay for the sheaf machinery.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Syntomic
namespace Big

variable {S T : Scheme.{u}}

/-- Postcomposition on the big syntomic slice categories. -/
abbrev map (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on the big syntomic slice categories. -/
abbrev pullback (f : T ⟶ S) : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor is continuous for the big syntomic slice topologies. -/
theorem map_isContinuous (f : T ⟶ S) :
    (map f).IsContinuous (Scheme.syntomicOverTopology T)
      (Scheme.syntomicOverTopology S) := sorry

/-- The postcomposition functor is cocontinuous for the big syntomic slice topologies. -/
theorem map_isCocontinuous (f : T ⟶ S) :
    (map f).IsCocontinuous (Scheme.syntomicOverTopology T)
      (Scheme.syntomicOverTopology S) := sorry

/-- The canonical postcomposition-pullback adjunction on big syntomic slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Pullback is continuous for the big syntomic slice topologies. -/
theorem pullback_isContinuous (f : T ⟶ S) :
    (pullback f).IsContinuous (Scheme.syntomicOverTopology S)
      (Scheme.syntomicOverTopology T) := sorry

/-- The `map f` presentation has the left-Kan-extension hypotheses used by lower shriek. -/
theorem map_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The `map f` presentation has the pointwise right-Kan-extension hypotheses used by direct
image computations. -/
theorem map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

end Big
end Syntomic
end Scheme
end AlgebraicGeometry
