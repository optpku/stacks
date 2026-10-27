/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion

/-!
# Étale restriction on small étale sites of algebraic spaces

An étale morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` induces the
postcomposition functor `j : X_étale ⥤ Y_étale` on small étale sites, and the
corresponding restriction of sheaves. The same postcomposition on the étale site of
algebraic spaces is `MorphismProperty.Over.map`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MorphismProperty

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Postcomposition with an étale morphism `f : X ⟶ Y` sends schemes étale over `X` to schemes
étale over `Y`. -/
def etaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    smallEtaleSite X ⥤ smallEtaleSite Y where
  obj U := @smallEtaleSite.mk S Y U.left (U.hom ≫ f)
    { of_etale := fun φ hφ ↦ by
        exact Etale.of_etale (f := f) (φ ≫ U.hom)
          (Etale.of_etale (f := U.hom) φ hφ) }
  map {U V} g := MorphismProperty.CostructuredArrow.homMk g.left trivial
    (by
      change (ofOverFunctor S).map g.left ≫ (V.hom ≫ f) = U.hom ≫ f
      rw [← Category.assoc, smallEtaleSite.w g]
      rfl)
  map_id := fun _ => MorphismProperty.CostructuredArrow.Hom.ext rfl
  map_comp := fun _ _ => MorphismProperty.CostructuredArrow.Hom.ext rfl

/-- The object map of `etaleRestriction f` is postcomposition of the structure morphism with
`f`. -/
@[simp]
theorem etaleRestriction_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (U : smallEtaleSite X) :
    (etaleRestriction f).obj U =
      @smallEtaleSite.mk S Y U.left (U.hom ≫ f)
        (@Etale.etale_comp S (ofOver U.left) X U.hom Y f U.prop ‹Etale f›) :=
  rfl

/-- The morphism map of `etaleRestriction f` retains the underlying morphism of schemes over `S`. -/
theorem etaleRestriction_map {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U V : smallEtaleSite X} (g : U ⟶ V) :
    ((etaleRestriction f).map g).left = g.left :=
  rfl

/-- Restriction along an identity morphism is the identity functor. -/
theorem etaleRestriction_id (X : AlgebraicSpace S) :
    etaleRestriction (𝟙 X) = 𝟭 (smallEtaleSite X) := by
  refine CategoryTheory.Functor.ext (fun U => ?_) (fun U V g => ?_)
  · refine MorphismProperty.Comma.ext rfl (Subsingleton.elim _ _) ?_
    change HEq (U.hom ≫ 𝟙 X) U.hom
    exact heq_of_eq (Category.comp_id U.hom)
  · apply MorphismProperty.CostructuredArrow.Hom.ext
    simp only [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.eqToHom_left,
      CategoryTheory.Functor.id_map]
    change g.left = (𝟙 _) ≫ g.left ≫ (𝟙 _)
    simp

/-- Restriction is functorial in the étale morphism. -/
theorem etaleRestriction_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale f] [Etale g] :
    etaleRestriction (f ≫ g) = etaleRestriction f ⋙ etaleRestriction g := by
  refine CategoryTheory.Functor.ext (fun U => ?_) (fun U V k => ?_)
  · refine MorphismProperty.Comma.ext rfl (Subsingleton.elim _ _) ?_
    change HEq (U.hom ≫ (f ≫ g)) ((U.hom ≫ f) ≫ g)
    exact heq_of_eq (Category.assoc U.hom f g).symm
  · apply MorphismProperty.CostructuredArrow.Hom.ext
    simp only [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.eqToHom_left]
    change k.left = (𝟙 _) ≫ k.left ≫ (𝟙 _)
    simp

/-- Postcomposition with an étale morphism of algebraic spaces is continuous for the small
étale topologies. -/
instance etaleRestriction_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (etaleRestriction f).IsContinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  sorry

/-- Postcomposition with an étale morphism of algebraic spaces is cocontinuous for the small
étale topologies. -/
instance etaleRestriction_isCocontinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (etaleRestriction f).IsCocontinuous (smallEtaleTopology X) (smallEtaleTopology Y) :=
  sorry

/-- Restriction of sheaves along an étale morphism of algebraic spaces, given by continuous
direct image of `etaleRestriction`. -/
abbrev etaleRestrictionSheaf {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (A : Type v) [Category.{w} A] :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  (etaleRestriction f).sheafPushforwardContinuous A
    (smallEtaleTopology X) (smallEtaleTopology Y)

/-- Sheaf restriction along an étale morphism is continuous sheaf pushforward of
`etaleRestriction`. -/
theorem etaleRestrictionSheaf_def {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (A : Type v) [Category.{w} A] :
    etaleRestrictionSheaf f A =
      (etaleRestriction f).sheafPushforwardContinuous A
        (smallEtaleTopology X) (smallEtaleTopology Y) :=
  rfl

/-- Sections of a restricted sheaf are the original sections on the postcomposed object. -/
theorem etaleRestrictionSheaf_obj_obj {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (A : Type v) [Category.{w} A] (G : Sheaf (smallEtaleTopology Y) A)
    (U : smallEtaleSite X) :
    ((etaleRestrictionSheaf f A).obj G).obj.obj (Opposite.op U) =
      G.obj.obj (Opposite.op ((etaleRestriction f).obj U)) :=
  rfl

/-- Postcomposition on the étale site of algebraic spaces along an étale morphism. -/
abbrev spacesEtaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    spacesEtaleSite X ⥤ spacesEtaleSite Y :=
  Over.map (Q := ⊤) (inferInstance : Etale f)

/-- `spacesEtaleRestriction f` is `MorphismProperty.Over.map` along `f`. -/
theorem spacesEtaleRestriction_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    spacesEtaleRestriction f = Over.map (Q := ⊤) (inferInstance : Etale f) :=
  rfl

/-- Postcomposition on the étale site of algebraic spaces is continuous. -/
instance spacesEtaleRestriction_isContinuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (spacesEtaleRestriction f).IsContinuous (spacesEtaleTopology X) (spacesEtaleTopology Y) :=
  sorry

/-- The identity-on-objects comparison of small and spaces étale sites intertwines étale
restriction. -/
def etaleRestriction_comp_inclusion {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    etaleRestriction f ⋙ smallEtaleToSpaces Y ≅
      smallEtaleToSpaces X ⋙ spacesEtaleRestriction f :=
  NatIso.ofComponents
    (fun U =>
      MorphismProperty.Over.isoMk (Iso.refl (ofOver U.left)) (by
        change 𝟙 (ofOver U.left) ≫ (U.hom ≫ f) = U.hom ≫ f
        exact Category.id_comp _))
    (by
      intro U V g
      apply MorphismProperty.Over.Hom.ext
      change (ofOverFunctor S).map g.left ≫ 𝟙 _ = 𝟙 _ ≫ (ofOverFunctor S).map g.left
      simp)

/-- Restriction of abelian sheaves along an étale morphism is additive. -/
instance etaleRestrictionSheaf_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).Additive where
  map_add := by
    intro F G a b
    ext U
    rfl

/-- Restriction of abelian sheaves along an étale morphism preserves homology. -/
instance etaleRestrictionSheaf_preservesHomology {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesHomology := by
  letI := ((etaleRestriction f).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology X) (smallEtaleTopology Y)).isLeftAdjoint
  infer_instance

/-- Restriction of abelian sheaves along an étale morphism preserves injective objects. -/
instance etaleRestrictionSheaf_preservesInjectiveObjects {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    (etaleRestrictionSheaf f AddCommGrpCat.{u + 1}).PreservesInjectiveObjects :=
  sorry

namespace Etale

/-- The top edge of a cartesian square with étale bottom edge is étale. -/
theorem fst_of_isPullback {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] : Etale h :=
  Etale.of_isPullback h_cart.flip inferInstance

end Etale

end AlgebraicGeometry.AlgebraicSpace
