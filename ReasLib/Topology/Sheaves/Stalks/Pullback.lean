/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Stalks.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of pullback sheaves

This file provides the canonical stalk comparison for pullback sheaves and the stalk map
associated to a morphism into a pushforward.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat
open TopCat.Presheaf

noncomputable section

universe w v u

namespace TopCat

/- Notation for inverse image on sheaves. The coefficient category is inferred from the expected
functor type. -/
scoped notation:max f:max "⁻¹" => TopCat.Sheaf.pullback _ f

end TopCat

namespace TopCat.Presheaf

section PullbackComparison

variable {A : Type u} [Category.{w} A] [HasColimits A]

/-- The presheaf pullback stalk comparison is natural in the presheaf on the target space. -/
@[reassoc, stacks 008H "inverse-image presheaf stalk comparison naturality"]
theorem stalkPullbackIso_hom_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {F G : Y.Presheaf A}
    (φ : F ⟶ G) (x : X) :
    (stalkFunctor A (f x)).map φ ≫ (stalkPullbackIso A f G x).hom =
      (stalkPullbackIso A f F x).hom ≫
        (stalkFunctor A x).map ((pullback A f).map φ) := sorry

/-- The inverse presheaf pullback stalk comparison is natural in the target presheaf. -/
@[reassoc, stacks 008H "inverse of inverse-image presheaf stalk comparison naturality"]
theorem stalkPullbackIso_inv_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {F G : Y.Presheaf A}
    (φ : F ⟶ G) (x : X) :
    (stalkFunctor A x).map ((pullback A f).map φ) ≫
        (stalkPullbackIso A f G x).inv =
      (stalkPullbackIso A f F x).inv ≫ (stalkFunctor A (f x)).map φ := sorry

end PullbackComparison

section PullbackNatIso

variable (A : Type u) [Category.{w} A] [HasColimits A]

/-- The forward natural transformation for the presheaf pullback stalk comparison. -/
@[stacks 008H "natural presheaf inverse-image stalk comparison"]
noncomputable def stalkPullbackNatTrans
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    stalkFunctor A (f x) ⟶ pullback A f ⋙ stalkFunctor A x where
  app F := (stalkPullbackIso A f F x).hom
  naturality _ _ φ := stalkPullbackIso_hom_naturality (A := A) f φ x

/-- The inverse natural transformation for the presheaf pullback stalk comparison. -/
@[stacks 008H "natural inverse presheaf inverse-image stalk comparison"]
noncomputable def stalkPullbackInvNatTrans
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    pullback A f ⋙ stalkFunctor A x ⟶ stalkFunctor A (f x) where
  app F := (stalkPullbackIso A f F x).inv
  naturality _ _ φ := stalkPullbackIso_inv_naturality (A := A) f φ x

/-- The forward and inverse presheaf pullback stalk transformations compose to the identity. -/
@[simp, stacks 008H "presheaf inverse-image stalk natural forward-inverse law"]
theorem stalkPullbackNatTrans_hom_inv_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    stalkPullbackNatTrans A f x ≫ stalkPullbackInvNatTrans A f x = 𝟙 _ := sorry

/-- The inverse and forward presheaf pullback stalk transformations compose to the identity. -/
@[simp, stacks 008H "presheaf inverse-image stalk natural inverse-forward law"]
theorem stalkPullbackNatTrans_inv_hom_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    stalkPullbackInvNatTrans A f x ≫ stalkPullbackNatTrans A f x = 𝟙 _ := sorry

/-- Taking a stalk commutes naturally with presheaf pullback. -/
@[stacks 008H "stalks of inverse-image presheaves"]
noncomputable def stalkPullbackNatIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    stalkFunctor A (f x) ≅ pullback A f ⋙ stalkFunctor A x :=
  { hom := stalkPullbackNatTrans A f x
    inv := stalkPullbackInvNatTrans A f x
    hom_inv_id := stalkPullbackNatTrans_hom_inv_id A f x
    inv_hom_id := stalkPullbackNatTrans_inv_hom_id A f x }

/-- Components of the presheaf pullback stalk natural isomorphism are the canonical objectwise
stalk isomorphisms. -/
@[simp, stacks 008H "inverse-image presheaf stalk natural isomorphism component"]
theorem stalkPullbackNatIso_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (F : Y.Presheaf A) (x : X) :
    (stalkPullbackNatIso A f x).app F = stalkPullbackIso A f F x := sorry

/-- The forward natural transformation of the presheaf pullback stalk natural isomorphism. -/
@[simp, stacks 008H "presheaf inverse-image stalk natural isomorphism hom"]
theorem stalkPullbackNatIso_hom
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    (stalkPullbackNatIso A f x).hom = stalkPullbackNatTrans A f x := sorry

/-- The inverse natural transformation of the presheaf pullback stalk natural isomorphism. -/
@[simp, stacks 008H "presheaf inverse-image stalk natural isomorphism inverse"]
theorem stalkPullbackNatIso_inv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    (stalkPullbackNatIso A f x).inv = stalkPullbackInvNatTrans A f x := sorry

/-- Forward components of the presheaf pullback stalk natural isomorphism are the canonical
stalk comparisons. -/
@[simp, stacks 008H "inverse-image presheaf stalk natural isomorphism hom component"]
theorem stalkPullbackNatIso_hom_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (F : Y.Presheaf A) (x : X) :
    (stalkPullbackNatIso A f x).hom.app F = (stalkPullbackIso A f F x).hom := sorry

/-- Inverse components of the presheaf pullback stalk natural isomorphism are the canonical
inverse comparisons. -/
@[simp, stacks 008H "inverse-image presheaf stalk natural isomorphism inverse component"]
theorem stalkPullbackNatIso_inv_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (F : Y.Presheaf A) (x : X) :
    (stalkPullbackNatIso A f x).inv.app F = (stalkPullbackIso A f F x).inv := sorry

end PullbackNatIso

end TopCat.Presheaf

namespace TopCat.Sheaf

section PullbackComparison

variable {A : Type u} [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The presheaf obtained by forgetting a sheaf and pulling it back along `f`. -/
@[stacks 008H "underlying presheaf of an inverse-image sheaf",
  stacks 008O "underlying abelian presheaf of an inverse-image sheaf"]
noncomputable abbrev pullbackPresheaf
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) : X.Presheaf A :=
  (TopCat.Presheaf.pullback A f).obj 𝒢.presheaf

/-- The stalkwise comparison from presheaf pullback to sheaf pullback, obtained from the
sheafification unit and `TopCat.Sheaf.pullbackIso`. -/
@[stacks 008H "presheaf-to-sheaf pullback stalk comparison",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk comparison"]
noncomputable def pullbackSheafifyStalkComparison
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (pullbackPresheaf f 𝒢).stalk x ⟶
      ((pullback A f).obj 𝒢).presheaf.stalk x :=
  TopCat.Presheaf.SheafificationStalk.comparison (pullbackPresheaf f 𝒢) x ≫
    (stalkFunctor A x).map ((forget A X).map ((pullbackIso A f).app 𝒢).inv)

/-- The explicit inverse from the stalk of a sheaf pullback to the stalk of the corresponding
presheaf pullback. -/
@[stacks 008H "inverse presheaf-to-sheaf pullback stalk comparison",
  stacks 008O "inverse abelian presheaf-to-sheaf pullback stalk comparison"]
noncomputable def pullbackSheafifyStalkComparisonInv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    ((pullback A f).obj 𝒢).presheaf.stalk x ⟶
      (pullbackPresheaf f 𝒢).stalk x :=
  (stalkFunctor A x).map ((forget A X).map ((pullbackIso A f).app 𝒢).hom) ≫
    TopCat.Presheaf.SheafificationStalk.comparisonInv (pullbackPresheaf f 𝒢) x

/-- The presheaf-to-sheaf pullback stalk comparison followed by its inverse is the identity. -/
@[simp, stacks 008H "presheaf-to-sheaf pullback stalk forward-inverse law",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk forward-inverse law"]
theorem pullbackSheafifyStalkComparison_hom_inv_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    pullbackSheafifyStalkComparison f 𝒢 x ≫
      pullbackSheafifyStalkComparisonInv f 𝒢 x = 𝟙 _ := sorry

/-- The inverse presheaf-to-sheaf pullback stalk comparison followed by the comparison is the
identity. -/
@[simp, stacks 008H "presheaf-to-sheaf pullback stalk inverse-forward law",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk inverse-forward law"]
theorem pullbackSheafifyStalkComparison_inv_hom_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    pullbackSheafifyStalkComparisonInv f 𝒢 x ≫
      pullbackSheafifyStalkComparison f 𝒢 x = 𝟙 _ := sorry

/-- The stalkwise isomorphism from presheaf pullback to sheaf pullback, with an explicitly owned
inverse. -/
@[stacks 008H "presheaf-to-sheaf pullback stalk isomorphism",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk isomorphism"]
noncomputable def pullbackSheafifyStalkIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (pullbackPresheaf f 𝒢).stalk x ≅
      ((pullback A f).obj 𝒢).presheaf.stalk x where
  hom := pullbackSheafifyStalkComparison f 𝒢 x
  inv := pullbackSheafifyStalkComparisonInv f 𝒢 x
  hom_inv_id := pullbackSheafifyStalkComparison_hom_inv_id f 𝒢 x
  inv_hom_id := pullbackSheafifyStalkComparison_inv_hom_id f 𝒢 x

/-- The forward map of `pullbackSheafifyStalkIso` is the named stalk comparison. -/
@[simp, stacks 008H "presheaf-to-sheaf pullback stalk isomorphism hom",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk isomorphism hom"]
theorem pullbackSheafifyStalkIso_hom
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (pullbackSheafifyStalkIso f 𝒢 x).hom = pullbackSheafifyStalkComparison f 𝒢 x := sorry

/-- The inverse map of `pullbackSheafifyStalkIso` is the named explicit inverse. -/
@[simp, stacks 008H "presheaf-to-sheaf pullback stalk isomorphism inverse",
  stacks 008O "abelian presheaf-to-sheaf pullback stalk isomorphism inverse"]
theorem pullbackSheafifyStalkIso_inv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (pullbackSheafifyStalkIso f 𝒢 x).inv = pullbackSheafifyStalkComparisonInv f 𝒢 x := sorry

/-- The canonical comparison from the original sheaf stalk to the pullback sheaf stalk. -/
@[stacks 008H "stalk comparison for inverse-image sheaves",
  stacks 008O "abelian stalk comparison for inverse-image sheaves"]
noncomputable def stalkPullbackComparison
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    𝒢.presheaf.stalk (f x) ⟶ ((pullback A f).obj 𝒢).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackHom A f 𝒢.presheaf x ≫
    pullbackSheafifyStalkComparison f 𝒢 x

/-- The explicit inverse from the pullback sheaf stalk to the original sheaf stalk. -/
@[stacks 008H "inverse stalk comparison for inverse-image sheaves",
  stacks 008O "inverse abelian stalk comparison for inverse-image sheaves"]
noncomputable def stalkPullbackComparisonInv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    ((pullback A f).obj 𝒢).presheaf.stalk x ⟶ 𝒢.presheaf.stalk (f x) :=
  pullbackSheafifyStalkComparisonInv f 𝒢 x ≫
    TopCat.Presheaf.stalkPullbackInv A f 𝒢.presheaf x

/-- The sheaf pullback stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 008H "inverse-image sheaf stalk forward-inverse law",
  stacks 008O "inverse-image abelian sheaf stalk forward-inverse law"]
theorem stalkPullbackComparison_hom_inv_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    stalkPullbackComparison f 𝒢 x ≫ stalkPullbackComparisonInv f 𝒢 x = 𝟙 _ := sorry

/-- The explicit inverse followed by the sheaf pullback stalk comparison is the identity. -/
@[simp, stacks 008H "inverse-image sheaf stalk inverse-forward law",
  stacks 008O "inverse-image abelian sheaf stalk inverse-forward law"]
theorem stalkPullbackComparison_inv_hom_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    stalkPullbackComparisonInv f 𝒢 x ≫ stalkPullbackComparison f 𝒢 x = 𝟙 _ := sorry

/-- The canonical stalk isomorphism for inverse image of a sheaf, with both directions explicitly
owned. -/
@[stacks 008H "stalks of inverse-image sheaves",
  stacks 008O "abelian stalks of inverse-image sheaves"]
noncomputable def stalkPullbackIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    𝒢.presheaf.stalk (f x) ≅ ((pullback A f).obj 𝒢).presheaf.stalk x where
  hom := stalkPullbackComparison f 𝒢 x
  inv := stalkPullbackComparisonInv f 𝒢 x
  hom_inv_id := stalkPullbackComparison_hom_inv_id f 𝒢 x
  inv_hom_id := stalkPullbackComparison_inv_hom_id f 𝒢 x

/-- The forward map of `stalkPullbackIso` is the named sheaf pullback stalk comparison. -/
@[simp, stacks 008H "inverse-image sheaf stalk isomorphism hom",
  stacks 008O "inverse-image abelian sheaf stalk isomorphism hom"]
theorem stalkPullbackIso_hom
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (stalkPullbackIso f 𝒢 x).hom = stalkPullbackComparison f 𝒢 x := sorry

/-- The inverse map of `stalkPullbackIso` is the named explicit inverse comparison. -/
@[simp, stacks 008H "inverse-image sheaf stalk isomorphism inverse",
  stacks 008O "inverse-image abelian sheaf stalk isomorphism inverse"]
theorem stalkPullbackIso_inv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (stalkPullbackIso f 𝒢 x).inv = stalkPullbackComparisonInv f 𝒢 x := sorry

/-- The sheaf pullback stalk comparison is natural in the sheaf on the target space. -/
@[reassoc, stacks 008H "inverse-image sheaf stalk comparison naturality",
  stacks 008O "inverse-image abelian sheaf stalk comparison naturality"]
theorem stalkPullbackComparison_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {𝒢 ℋ : Y.Sheaf A}
    (φ : 𝒢 ⟶ ℋ) (x : X) :
    (stalkFunctor A (f x)).map φ.hom ≫ stalkPullbackComparison f ℋ x =
      stalkPullbackComparison f 𝒢 x ≫
        (stalkFunctor A x).map ((pullback A f).map φ).hom := sorry

/-- The explicit inverse sheaf pullback stalk comparison is natural in the target sheaf. -/
@[reassoc, stacks 008H "inverse of the sheaf pullback stalk comparison naturality",
  stacks 008O "inverse of the abelian sheaf pullback stalk comparison naturality"]
theorem stalkPullbackComparisonInv_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {𝒢 ℋ : Y.Sheaf A}
    (φ : 𝒢 ⟶ ℋ) (x : X) :
    (stalkFunctor A x).map ((pullback A f).map φ).hom ≫
        stalkPullbackComparisonInv f ℋ x =
      stalkPullbackComparisonInv f 𝒢 x ≫
        (stalkFunctor A (f x)).map φ.hom := sorry

/-- The sheaf pullback stalk comparison is natural in the sheaf on the target space. -/
@[reassoc, stacks 008H "inverse-image sheaf stalk comparison naturality",
  stacks 008O "inverse-image abelian sheaf stalk comparison naturality"]
theorem stalkPullbackIso_hom_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {𝒢 ℋ : Y.Sheaf A}
    (φ : 𝒢 ⟶ ℋ) (x : X) :
    (stalkFunctor A (f x)).map φ.hom ≫ (stalkPullbackIso f ℋ x).hom =
      (stalkPullbackIso f 𝒢 x).hom ≫
        (stalkFunctor A x).map ((pullback A f).map φ).hom := sorry

/-- The sheaf pullback stalk inverse is natural in the sheaf on the target space. -/
@[reassoc, stacks 008H "inverse of inverse-image sheaf stalk comparison naturality",
  stacks 008O "inverse of inverse-image abelian sheaf stalk comparison naturality"]
theorem stalkPullbackIso_inv_naturality
    {X Y : TopCat.{w}} (f : X ⟶ Y) {𝒢 ℋ : Y.Sheaf A}
    (φ : 𝒢 ⟶ ℋ) (x : X) :
    (stalkFunctor A x).map ((pullback A f).map φ).hom ≫
        (stalkPullbackIso f ℋ x).inv =
      (stalkPullbackIso f 𝒢 x).inv ≫
        (stalkFunctor A (f x)).map φ.hom := sorry

end PullbackComparison

section PullbackNatIso

variable (A : Type u) [Category.{w} A] {FA : A → A → Type v} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
variable [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

/-- The forward natural transformation for the sheaf pullback stalk comparison. -/
@[stacks 008H "natural inverse-image sheaf stalk comparison",
  stacks 008O "natural inverse-image abelian sheaf stalk comparison"]
noncomputable def stalkPullbackNatTrans
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    forget A Y ⋙ stalkFunctor A (f x) ⟶
      pullback A f ⋙ forget A X ⋙ stalkFunctor A x where
  app 𝒢 := stalkPullbackComparison f 𝒢 x
  naturality _ _ φ := stalkPullbackComparison_naturality f φ x

/-- The inverse natural transformation for the sheaf pullback stalk comparison. -/
@[stacks 008H "natural inverse inverse-image sheaf stalk comparison",
  stacks 008O "natural inverse inverse-image abelian sheaf stalk comparison"]
noncomputable def stalkPullbackInvNatTrans
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    pullback A f ⋙ forget A X ⋙ stalkFunctor A x ⟶
      forget A Y ⋙ stalkFunctor A (f x) where
  app 𝒢 := stalkPullbackComparisonInv f 𝒢 x
  naturality _ _ φ := stalkPullbackComparisonInv_naturality f φ x

/-- The forward and inverse sheaf pullback stalk transformations compose to the identity. -/
@[simp, stacks 008H "sheaf inverse-image stalk natural forward-inverse law",
  stacks 008O "abelian sheaf inverse-image stalk natural forward-inverse law"]
theorem stalkPullbackNatTrans_hom_inv_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.stalkPullbackNatTrans A f x ≫
        TopCat.Sheaf.stalkPullbackInvNatTrans A f x = 𝟙 _ := sorry

/-- The inverse and forward sheaf pullback stalk transformations compose to the identity. -/
@[simp, stacks 008H "sheaf inverse-image stalk natural inverse-forward law",
  stacks 008O "abelian sheaf inverse-image stalk natural inverse-forward law"]
theorem stalkPullbackNatTrans_inv_hom_id
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    TopCat.Sheaf.stalkPullbackInvNatTrans A f x ≫
        TopCat.Sheaf.stalkPullbackNatTrans A f x = 𝟙 _ := sorry

/-- Taking a stalk commutes naturally with pullback of sheaves. -/
@[stacks 008H "stalks of inverse-image sheaves, natural form",
  stacks 008O "abelian stalks of inverse-image sheaves, natural form"]
noncomputable def stalkPullbackNatIso
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    forget A Y ⋙ stalkFunctor A (f x) ≅
      pullback A f ⋙ forget A X ⋙ stalkFunctor A x :=
  { hom := TopCat.Sheaf.stalkPullbackNatTrans A f x
    inv := TopCat.Sheaf.stalkPullbackInvNatTrans A f x
    hom_inv_id := TopCat.Sheaf.stalkPullbackNatTrans_hom_inv_id A f x
    inv_hom_id := TopCat.Sheaf.stalkPullbackNatTrans_inv_hom_id A f x }

/-- Components of the sheaf pullback stalk natural isomorphism are the canonical objectwise
stalk isomorphisms. -/
@[simp, stacks 008H "inverse-image sheaf stalk natural isomorphism component",
  stacks 008O "inverse-image abelian sheaf stalk natural isomorphism component"]
theorem stalkPullbackNatIso_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (stalkPullbackNatIso A f x).app 𝒢 = stalkPullbackIso f 𝒢 x := sorry

/-- The forward natural transformation of the sheaf pullback stalk natural isomorphism. -/
@[simp, stacks 008H "inverse-image sheaf stalk natural isomorphism hom",
  stacks 008O "inverse-image abelian sheaf stalk natural isomorphism hom"]
theorem stalkPullbackNatIso_hom
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    (stalkPullbackNatIso A f x).hom = TopCat.Sheaf.stalkPullbackNatTrans A f x := sorry

/-- The inverse natural transformation of the sheaf pullback stalk natural isomorphism. -/
@[simp, stacks 008H "inverse-image sheaf stalk natural isomorphism inverse",
  stacks 008O "inverse-image abelian sheaf stalk natural isomorphism inverse"]
theorem stalkPullbackNatIso_inv
    {X Y : TopCat.{w}} (f : X ⟶ Y) (x : X) :
    (stalkPullbackNatIso A f x).inv = TopCat.Sheaf.stalkPullbackInvNatTrans A f x := sorry

/-- Forward components of the sheaf pullback stalk natural isomorphism are the named stalk
comparisons. -/
@[simp, stacks 008H "inverse-image sheaf stalk natural isomorphism hom component",
  stacks 008O "inverse-image abelian sheaf stalk natural isomorphism hom component"]
theorem stalkPullbackNatIso_hom_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (stalkPullbackNatIso A f x).hom.app 𝒢 = stalkPullbackComparison f 𝒢 x := sorry

/-- Inverse components of the sheaf pullback stalk natural isomorphism are the named explicit
inverse comparisons. -/
@[simp, stacks 008H "inverse-image sheaf stalk natural isomorphism inverse component",
  stacks 008O "inverse-image abelian sheaf stalk natural isomorphism inverse component"]
theorem stalkPullbackNatIso_inv_app
    {X Y : TopCat.{w}} (f : X ⟶ Y) (𝒢 : Y.Sheaf A) (x : X) :
    (stalkPullbackNatIso A f x).inv.app 𝒢 = stalkPullbackComparisonInv f 𝒢 x := sorry

end PullbackNatIso

section StalkMap

variable {A : Type u} [Category.{v} A] [HasColimits A]

/-- The map on stalks induced by a morphism from a sheaf to the pushforward of another sheaf. -/
@[stacks 008H "stalk map from a pushforward comparison"]
def stalkMap {X Y : TopCat.{v}} (f : X ⟶ Y) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (x : X) :
    𝒢.presheaf.stalk (f x) ⟶ ℱ.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor A (f x)).map φ.1 ≫
    ℱ.presheaf.stalkPushforward A f x

/-- The stalk map induced by a composite morphism into iterated pushforwards is the composite of
the two induced stalk maps. -/
@[stacks 008H "composition of stalk maps from pushforward comparisons"]
theorem stalkMap_comp {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {ℱ : X.Sheaf A} {𝒢 : Y.Sheaf A} {ℋ : Z.Sheaf A}
    (φ : 𝒢 ⟶ (pushforward A f).obj ℱ) (ψ : ℋ ⟶ (pushforward A g).obj 𝒢) (x : X) :
    stalkMap (f ≫ g) (ψ ≫ (pushforward A g).map φ) x =
      stalkMap g ψ (f x) ≫ stalkMap f φ x := sorry

end StalkMap

end TopCat.Sheaf
