/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Topology
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Big fppf sheaf functors on algebraic spaces

A morphism of algebraic spaces induces adjoint sheaf functors on the big
fppf slice sites. The underlying functors are the
canonical postcomposition and pullback functors on over-categories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace Fppf
namespace Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition admits pointwise left Kan extensions of type-valued
presheaves on the source slice. -/
instance map_op_hasPointwiseLeftKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasPointwiseLeftKanExtension P := by
  intro U
  change HasColimit (CostructuredArrow.proj (Over.map f).op U ⋙ P)
  infer_instance

/-- Postcomposition admits pointwise right Kan extensions of type-valued
presheaves on the source slice. -/
instance map_op_hasPointwiseRightKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (Over.map f).op.HasPointwiseRightKanExtension P := by
  intro U
  change HasLimit (StructuredArrow.proj U (Over.map f).op ⋙ P)
  infer_instance

/-- Lower shriek on big fppf sheaves preserves pullbacks. -/
instance lowerShriek_preservesPullbacks (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (CategoryTheory.Over.Site.lowerShriek.{u + 1, u + 1, u + 1}
      (fppfTopology S) f) := sorry

/-- Lower shriek on big fppf sheaves preserves equalizers. -/
instance lowerShriek_preservesEqualizers (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingParallelPair (CategoryTheory.Over.Site.lowerShriek.{u + 1, u + 1, u + 1}
      (fppfTopology S) f) := sorry

end Big
end Fppf
end AlgebraicSpace
end AlgebraicGeometry
