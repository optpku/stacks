/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SpaceComparisonGeometry
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage

/-!
# Big-versus-small étale pushforward comparison

For a morphism `f : F ⟶ G` of algebraic spaces, the restriction of the CFG
pushforward `f_* ℱ` to `G_étale` is canonically identified with the small étale
pushforward of the restriction of `ℱ` to `F_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite FiberedCategoryOver.Groupoids
open CategoryTheory.CategoryOfElements
open Limits.Types

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The CFG étale pushforward of a sheaf with successor-universe coefficients.
Each actual comma diagram already has coefficients and indices in this universe. -/
abbrev etalePushforward {F G : AlgebraicSpace S} (f : F ⟶ G) :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf G.toGroupoids.etaleTopology (Type (u + 1)) :=
  (toFunctor (toGroupoids.map f)).sheafPushforwardOfSmallSections.{u + 1, u, u + 1, u, u + 1}
    F.toGroupoids.etaleTopology G.toGroupoids.etaleTopology

section CompareTypeSucc

variable {F G : AlgebraicSpace S} (f : F ⟶ G)
variable (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))

/-- Restriction of compatible families from the CFG Kan comma category to the
small-étale Kan comma category. -/
def compareLimitHom (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ⟶ limit (compareSmallDiag f ℱ V) :=
  limit.pre (compareBigDiag f ℱ V) (compareIndexMap f V) ≫
    (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).hom

/-- Restriction of a small-étale compatible family to the atlas cover `U₀`. -/
def compareCoverSection (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶
      ℱ.obj.obj (op ((GroupoidsOver.smallEtaleToGroupoids F).obj (coverSite f V))) :=
  (HasLimit.isoOfNatIso (compareDiagIso f ℱ V)).inv ≫
    limit.π (compareIndexMap f V ⋙ compareBigDiag f ℱ V) (coverIndex f V)

/-- The family of sections of `ℱ` on `T ×_{F ×_G V} U₀` obtained by restricting the atlas
cover section. -/
def compareFibreSection (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ ℱ.obj.obj (op (compareFibreObj f j)) :=
  compareCoverSection f ℱ V ≫ ℱ.obj.map (compareFibreToCover f j).op

/-- Compatibility of the one-arrow covering family on `T ×_{F ×_G V} U₀`. -/
private theorem compareFibreSection_compatible (V : smallEtaleSite G)
    (j : compareBigIndex f V) :
    ∀ ⦃W : F.toGroupoids.total⦄ ⦃i k : Unit⦄
      (a : W ⟶ compareFibreObj f j) (b : W ⟶ compareFibreObj f j),
      a ≫ compareFibreToBig f j = b ≫ compareFibreToBig f j →
        compareFibreSection f ℱ V j ≫ ℱ.obj.map a.op =
          compareFibreSection f ℱ V j ≫ ℱ.obj.map b.op :=
  sorry

/-- Component of the reverse comparison cone at a CFG comma object. -/
def compareInvπ (V : smallEtaleSite G) (j : compareBigIndex f V) :
    limit (compareSmallDiag f ℱ V) ⟶ (compareBigDiag f ℱ V).obj j :=
  ℱ.property.amalgamateOfArrows
    (fun _ : Unit => compareFibreToBig f j)
    (compareFibre_cover_mem f j)
    (fun _ => compareFibreSection f ℱ V j)
    (by exact compareFibreSection_compatible f ℱ V j)

/-- Extension of a small-étale compatible family to a CFG compatible family, by
amalgamating along the étale cover `T ×_{F ×_G V} U₀ ⟶ T`. -/
def compareLimitInv (V : smallEtaleSite G) :
    limit (compareSmallDiag f ℱ V) ⟶ limit (compareBigDiag f ℱ V) :=
  limit.lift (compareBigDiag f ℱ V)
    { pt := limit (compareSmallDiag f ℱ V)
      π :=
        { app := compareInvπ f ℱ V
          naturality := sorry } }

/-- Canonical identification of the two Kan-extension limits at `V`. -/
def compareLimitIso (V : smallEtaleSite G) :
    limit (compareBigDiag f ℱ V) ≅ limit (compareSmallDiag f ℱ V) where
  hom := compareLimitHom f ℱ V
  inv := compareLimitInv f ℱ V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The spaces-étale extension of `ℱ |_{F_étale}` used by `f_small,*`. -/
abbrev compareSmallExtended :
    Sheaf (spacesEtaleTopology F) (Type (u + 1)) :=
  ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology F) (spacesEtaleTopology F)).obj
    ((restrictEtale F).obj ℱ)

/-- Sectionwise identification of `(f_* ℱ)(u_G(V))` with
`f_small,* (ℱ |_{F_étale})(V)`. -/
def compareBigSmall_app (V : smallEtaleSite G) :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj.obj (op V) ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj.obj (op V) :=
  (sheafPushforwardContinuousObjObjIso (GroupoidsOver.smallEtaleToGroupoids G) (Type (u + 1))
      ((etalePushforward f).obj ℱ) V) ≪≫
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension
      (toFunctor (toGroupoids.map f)).op ℱ.obj
      (op ((GroupoidsOver.smallEtaleToGroupoids G).obj V))).isoLimit ≪≫
      compareLimitIso f ℱ V ≪≫
        ((AlgebraicGeometry.AlgebraicSpace.smallEtaleToSpaces F).op.ranObjObjIsoLimit
            ((restrictEtale F).obj ℱ).obj
            (op ((etaleBaseChange f).obj V))).symm ≪≫
          (sheafPushforwardContinuousObjObjIso (etaleBaseChange f) (Type (u + 1))
              (compareSmallExtended ℱ) V).symm

/-- Underlying presheaf identification of the two composites. -/
def compareBigSmallPresheaf :
    ((restrictEtale G).obj ((etalePushforward f).obj ℱ)).obj ≅
      ((sheafPushforwardType f).obj ((restrictEtale F).obj ℱ)).obj :=
  NatIso.ofComponents (fun V => compareBigSmall_app f ℱ V.unop) sorry

/-- The canonical identification
`(f_* ℱ)|_{G_étale} = f_small,* (ℱ |_{F_étale})` of sheaves on `G_étale`. -/
def compareBigSmall :
    (restrictEtale G).obj ((etalePushforward f).obj ℱ) ≅
      (sheafPushforwardType f).obj ((restrictEtale F).obj ℱ) where
  hom := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).hom
  inv := CategoryTheory.ObjectProperty.homMk (compareBigSmallPresheaf f ℱ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `compareBigSmall` is the sectionwise identification `compareBigSmall_app`. -/
theorem compareBigSmall_app_eq (V : smallEtaleSite G) :
    ((sheafToPresheaf (smallEtaleTopology G) (Type (u + 1))).mapIso
          (compareBigSmall f ℱ)).app (op V) =
      compareBigSmall_app f ℱ V :=
  sorry

/-- The identification is natural in the étale sheaf `ℱ`. -/
theorem compareBigSmall_natural
    {ℱ 𝒢 : Sheaf F.toGroupoids.etaleTopology (Type (u + 1))} (τ : ℱ ⟶ 𝒢) :
    (restrictEtale G).map ((etalePushforward f).map τ) ≫ (compareBigSmall f 𝒢).hom =
      (compareBigSmall f ℱ).hom ≫
        (sheafPushforwardType f).map ((restrictEtale F).map τ) :=
  sorry

end CompareTypeSucc

end AlgebraicGeometry.AlgebraicSpace
