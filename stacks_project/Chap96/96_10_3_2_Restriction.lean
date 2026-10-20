/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap96.«96_10_3_1_Restriction»

/-!
# Inclusion of the small étale topos of an algebraic space

The tautological functor `u : U_étale ⥤ (S_U)_étale` of
`smallEtaleToGroupoids` is continuous and cocontinuous. The associated
morphism of topoi `i_U : Sh(U_étale) ⟶ Sh((S_U)_étale)` has inverse image
isomorphic to `restrictEtale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The morphism of topoi `i_U : Sh(U_étale) ⟶ Sh((S_U)_étale)` presented by the
tautological functor `smallEtaleToGroupoids U`. -/
def inclusionTopos (U : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology U) (Type (u + 1))]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ Type (u + 1),
      (smallEtaleToGroupoids U).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn U.toGroupoids.etaleTopology (smallEtaleTopology U) :=
  (smallEtaleToGroupoids U).morphismOfTopoiInOfCocontinuous
    (smallEtaleTopology U) U.toGroupoids.etaleTopology

/-- The inverse image of `inclusionTopos` is cocontinuous sheaf pullback along
`smallEtaleToGroupoids`. -/
theorem inclusionTopos_inverseImage (U : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology U) (Type (u + 1))]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ Type (u + 1),
      (smallEtaleToGroupoids U).op.HasPointwiseRightKanExtension P] :
    (inclusionTopos U).inverseImage =
      (smallEtaleToGroupoids U).sheafPullbackCocontinuous (Type (u + 1))
        (smallEtaleTopology U) U.toGroupoids.etaleTopology :=
  sorry

/-- The direct image of `inclusionTopos` is cocontinuous sheaf pushforward along
`smallEtaleToGroupoids`. -/
theorem inclusionTopos_pushforward (U : AlgebraicSpace S)
    [HasSheafify (smallEtaleTopology U) (Type (u + 1))]
    [∀ P : (smallEtaleSite U)ᵒᵖ ⥤ Type (u + 1),
      (smallEtaleToGroupoids U).op.HasPointwiseRightKanExtension P] :
    (inclusionTopos U).pushforward =
      (smallEtaleToGroupoids U).sheafPushforwardCocontinuous (Type (u + 1))
        (smallEtaleTopology U) U.toGroupoids.etaleTopology :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
