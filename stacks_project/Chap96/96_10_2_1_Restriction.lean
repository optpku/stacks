module

public import stacks_project.Chap96.Lemma_96_10_1_Comparison

/-!
# Restriction of étale sheaves along a representing algebraic space

Given an equivalence `j : F.toGroupoids ≌ X`, restriction of an étale sheaf on
`X` to `F_étale` is continuous sheaf pushforward along `smallEtaleFunctor`.
This is the inverse image of `i_F` and the direct image of `π_F`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}
variable (F : AlgebraicSpace S) (X : GroupoidsOver S) (j : F.toGroupoids ≌ X)
variable [HasSheafify (smallEtaleTopology F) (Type u)]
variable [∀ P : (smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X j).op.HasPointwiseRightKanExtension P]
variable [∀ P : (smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X j).op.HasPointwiseRightKanExtension P]
variable [(smallEtaleTopology F).HasSheafCompose (forget RingCat.{u})]
variable [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X j).op]
variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X j).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((smallEtaleFunctor F X j).sheafPullback (Type u) (smallEtaleTopology F)
      X.etaleTopology)]

/-- Restriction of a set-valued étale sheaf on `X` to the small étale site of a
representing algebraic space `F`. This is `ℱ|_{F_étale}`, implemented as
continuous sheaf pushforward along `smallEtaleFunctor`. -/
def restrictSheaf :
    Sheaf X.etaleTopology (Type u) ⥤ Sheaf (smallEtaleTopology F) (Type u) :=
  (smallEtaleFunctor F X j).sheafPushforwardContinuous (Type u)
    (smallEtaleTopology F) X.etaleTopology

/-- Restriction equals the inverse image of the morphism of topoi `i_F`. -/
theorem restrictSheaf_eq_inverseImage :
    restrictSheaf F X j = (inclusionToTopos F X j)⁻¹ :=
  sorry

/-- Restriction equals the direct image of the morphism of topoi `π_F`. -/
theorem restrictSheaf_eq_piPushforward :
    restrictSheaf F X j = (piToTopos F X j).pushforward :=
  sorry

/-- Sections of a restricted sheaf over `U` are the original sections on `u(U)`. -/
theorem restrictSheaf_obj (ℱ : Sheaf X.etaleTopology (Type u))
    (U : smallEtaleSite F) :
    ((restrictSheaf F X j).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((smallEtaleFunctor F X j).obj U)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
