/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Degreewise
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
import StacksCheckRecall

/-!
@stack 0183

# Lemma 14.19.2 compatibility facade

The finite truncated-simplex indexing and pointwise right-Kan-extension API is owned by
`ReasLib.AlgebraicTopology.SimplexCategory.Truncated.{Finite,KanExtension}`.
This module retains the historical Chapter 14 import path and source traceability.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable (m n : ℕ) (U : SimplicialObject.Truncated C m)

open SimplicialObject.Truncated.coskeleton

/- Lemma 14.19.2: the matching category and finite-limit pointwise right Kan extension are
owned by the neutral truncated-simplex support API. -/
#check SimplexCategory.Truncated.matchingIndex
#check SimplexCategory.Truncated.matchingIndex.finCategory
#check SimplexCategory.Truncated.inclusion.pointwise.right.kanExtension
#check degree.Index
#check degree.Index.map
#check degree.diagram

/- The canonical degreewise coskeleton formula is the objectwise right-Kan-extension limit
coordinate. -/
#check Functor.RightKanExtension.objIsoLimit

@[stacks 0183]
#check (degree.isoLimit U ⦋n⦌ :
  U.coskeleton.obj (op ⦋n⦌) ≅
    limit (degree.diagram U ⦋n⦌))

variable (f : degree.Index m ⦋n⦌)

/- The companion projection formula is the generic objectwise right-Kan-extension theorem. -/
#check Functor.RightKanExtension.objIsoLimit.hom_π

#check (degree.isoLimit.hom_π U f :
  (degree.isoLimit U ⦋n⦌).hom ≫ limit.π (degree.diagram U ⦋n⦌) f =
    U.coskeleton.map f.hom ≫
      ((SimplexCategory.Truncated.inclusion m).op.rightKanExtensionCounit U).app f.right)

variable (Δ Δ' : SimplexCategory) (φ : Δ ⟶ Δ')

/- The objectwise right-Kan-extension owner expresses the simplicial structure map as the limit
comparison induced by precomposition with `φ.op`. -/
@[stacks 0183 "Lemma 14.19.2: coskeleton map between degreewise limits"]
#check
  (degree.limitMap U φ :
    limit (degree.diagram U Δ') ⟶ limit (degree.diagram U Δ))

variable (g : degree.Index m Δ)

/- The canonical objectwise limit coordinate says that the coskeleton structure map sends each
projection to the projection indexed by the reindexed structured arrow. -/
@[stacks 0183 "Lemma 14.19.2: coskeleton structure map on limit projections"]
#check
  (degree.isoLimit.map_π U φ g :
    (degree.isoLimit U Δ').inv ≫
        U.coskeleton.map φ.op ≫
        (degree.isoLimit U Δ).hom ≫
      limit.π (degree.diagram U Δ) g =
    limit.π (degree.diagram U Δ') ((degree.Index.map φ).obj g))

end CategoryTheory
