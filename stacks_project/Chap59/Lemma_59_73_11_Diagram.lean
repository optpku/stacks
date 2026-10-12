/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_71_5
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale.FiniteLocallyConstant

section Property

variable {A : Type v} [Category.{w} A]
variable (P : ∀ {Z : Scheme.{u}},
    ObjectProperty (CategoryTheory.Sheaf Z.smallEtaleTopology A))

/-- The full subcategory of small étale sheaves selected by `P`. -/
public abbrev fullSubcategory (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (P (Z := X))

end Property

section SetProperty

variable [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
variable [∀ {S : Scheme.{u}} (U : S.Etale),
    HasWeakSheafify (S.smallEtaleTopology.over U) (Type (u + 1))]

/-- Full subcategory of finite locally constant sheaves of sets. -/
public abbrev setFullSubcategory (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Sheaf X.smallEtaleTopology (Type (u + 1)) ↦
      Sheaf.IsFiniteLocallyConstant F)

/-- Object property of finite locally constant sheaves of sets. -/
public abbrev setProperty {X : Scheme.{u}} :
    ObjectProperty (CategoryTheory.Sheaf X.smallEtaleTopology (Type (u + 1))) :=
  fun F ↦ Sheaf.IsFiniteLocallyConstant F

end SetProperty

section AddCommGrpProperty

variable [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ {S : Scheme.{u}} (U : S.Etale),
    HasWeakSheafify (S.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]

/-- Full subcategory of finite locally constant abelian sheaves. -/
public abbrev addCommGrpFullSubcategory (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
      Sheaf.IsFiniteLocallyConstantAddCommGrp F)

/-- Object property of finite locally constant abelian sheaves. -/
public abbrev addCommGrpProperty {X : Scheme.{u}} :
    ObjectProperty (CategoryTheory.Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  fun F ↦ Sheaf.IsFiniteLocallyConstantAddCommGrp F

end AddCommGrpProperty

/-- Full subcategory of finite-type locally constant sheaves of modules. -/
public abbrev moduleFullSubcategory (Λ : Type v) [Ring Λ] [IsNoetherianRing Λ]
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ) ↦
      Sheaf.IsFiniteTypeLocallyConstantModule F)

/-- Object property of finite-type locally constant sheaves of modules. -/
public abbrev moduleProperty (Λ : Type v) [Ring Λ] [IsNoetherianRing Λ]
    [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ {S : Scheme.{u}} (U : S.Etale),
      HasWeakSheafify (S.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    {X : Scheme.{u}} :
    ObjectProperty (CategoryTheory.Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  fun F ↦ Sheaf.IsFiniteTypeLocallyConstantModule F

section InverseImage

variable {A : Type v} [Category.{w} A]
variable [∀ {S : Scheme.{u}}, HasWeakSheafify S.smallEtaleTopology A]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S) (Q : S.Etaleᵒᵖ ⥤ A),
    (Scheme.smallEtalePullback f).op.HasLeftKanExtension Q]
variable (P : ∀ {Z : Scheme.{u}},
    ObjectProperty (CategoryTheory.Sheaf Z.smallEtaleTopology A))

/-- Inverse image along `f` preserves the object property `P`. -/
public theorem isStableUnderInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : CategoryTheory.Sheaf Y.smallEtaleTopology A) (hF : P F) :
    P ((Sheaf.smallEtaleInverseImage f A).obj F) :=
  sorry

/-- Inverse image along `f` lifts to the selected full subcategories. -/
public def map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fullSubcategory P Y ⥤ fullSubcategory P X :=
  ObjectProperty.lift (P (Z := X))
    ((P (Z := Y)).ι ⋙ Sheaf.smallEtaleInverseImage f A)
    (fun F ↦ isStableUnderInverseImage P f F.obj F.property)

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : I} (hij : i ≤ j),
    IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
variable [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
variable [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
variable (c : Cone D)

/-- Inverse image from a stage to the limit. -/
public def stageComparison (i : I) :
    fullSubcategory P (D.obj (OrderDual.toDual i)) ⥤ fullSubcategory P c.pt :=
  map P (c.π.app (OrderDual.toDual i))

/-- The Cat-valued diagram of selected full subcategories on the stages. -/
public def diagram : I ⥤ Cat where
  obj i := Cat.of (fullSubcategory P (D.obj (OrderDual.toDual i)))
  map {i j} f :=
    (map P (OrderDualInverseSystem.transitionMap D (CategoryTheory.leOfHom f))).toCatHom
  map_id := sorry
  map_comp := sorry

/-- Inverse-image cocone with apex the selected full subcategory on the limit. -/
public def cocone : Cocone (diagram P D) where
  pt := Cat.of (fullSubcategory P c.pt)
  ι :=
    { app := fun i ↦ (stageComparison P D c i).toCatHom
      naturality := sorry }

/-- Origin-stage data of a selected sheaf on the limit. -/
public structure Origin (hc : IsLimit c)
    (F : fullSubcategory P c.pt) where
  index : I
  sheaf : fullSubcategory P (D.obj (OrderDual.toDual index))
  iso : (stageComparison P D c index).obj sheaf ≅ F

/-- Existence of an origin stage for a selected sheaf on the limit. -/
public theorem nonempty_origin (hc : IsLimit c) (F : fullSubcategory P c.pt) :
    Nonempty (Origin P D c hc F) :=
  sorry

/-- A chosen origin-stage presentation of a selected sheaf on the limit. -/
public noncomputable def origin (hc : IsLimit c) (F : fullSubcategory P c.pt) :
    Origin P D c hc F :=
  Classical.choice (nonempty_origin P D c hc F)

/-- Origin-stage data of a morphism of selected sheaves on the limit. -/
public structure OriginMap (hc : IsLimit c)
    {F G : fullSubcategory P c.pt} (f : F ⟶ G) where
  index : I
  le_src : (origin P D c hc F).index ≤ index
  le_tgt : (origin P D c hc G).index ≤ index
  hom :
    (map P (OrderDualInverseSystem.transitionMap D le_src)).obj
        (origin P D c hc F).sheaf ⟶
      (map P (OrderDualInverseSystem.transitionMap D le_tgt)).obj
        (origin P D c hc G).sheaf

/-- Existence of an origin-stage presentation of a morphism on the limit. -/
public theorem nonempty_originMap (hc : IsLimit c)
    {F G : fullSubcategory P c.pt} (f : F ⟶ G) :
    Nonempty (OriginMap P D c hc f) :=
  sorry

/-- A chosen later-stage presentation of a morphism on the limit. -/
public noncomputable def originMap (hc : IsLimit c)
    {F G : fullSubcategory P c.pt} (f : F ⟶ G) :
    OriginMap P D c hc f :=
  Classical.choice (nonempty_originMap P D c hc f)

/-- Cocone legs identify an origin sheaf with its inverse image at a later stage. -/
public theorem desc_obj_transition (hc : IsLimit c)
    (s : Cocone (diagram P D))
    {F : fullSubcategory P c.pt} {j : I}
    (hj : (origin P D c hc F).index ≤ j) :
    (s.ι.app (origin P D c hc F).index).toFunctor.obj (origin P D c hc F).sheaf =
      (s.ι.app j).toFunctor.obj
        ((map P (OrderDualInverseSystem.transitionMap D hj)).obj
          (origin P D c hc F).sheaf) :=
  sorry

/-- Mediating `Cat` morphism from the selected subcategory on the limit. -/
public noncomputable def desc (hc : IsLimit c) (s : Cocone (diagram P D)) :
    (cocone P D c).pt ⟶ s.pt :=
  Functor.toCatHom
    { obj := fun F ↦
        (s.ι.app (origin P D c hc F).index).toFunctor.obj (origin P D c hc F).sheaf
      map := fun {F G} f ↦
        eqToHom (desc_obj_transition P D c hc s (originMap P D c hc f).le_src) ≫
          (s.ι.app (originMap P D c hc f).index).toFunctor.map
            (originMap P D c hc f).hom ≫
          eqToHom (desc_obj_transition P D c hc s (originMap P D c hc f).le_tgt).symm
      map_id := sorry
      map_comp := sorry }

/-- Canonical comparison in `Cat` from a chosen filtered colimit of the stage diagram. -/
public noncomputable def comparison [HasColimit (diagram P D)] :
    colimit (diagram P D) ⟶ Cat.of (fullSubcategory P c.pt) :=
  colimit.desc (diagram P D) (cocone P D c)

end InverseImage

/-- Cat-valued diagram of finite locally constant sheaves of sets. -/
public abbrev setDiagram := @diagram (Type (u + 1))

/-- Inverse-image cocone of finite locally constant sheaves of sets. -/
public abbrev setCocone := @cocone (Type (u + 1))

/-- Comparison from the filtered colimit of finite locally constant sheaves of sets. -/
public abbrev setComparison := @comparison (Type (u + 1))

/-- Mediating `Cat` morphism for finite locally constant sheaves of sets. -/
public abbrev setDesc := @desc (Type (u + 1))

/-- Cat-valued diagram of finite locally constant abelian sheaves. -/
public abbrev addCommGrpDiagram := @diagram AddCommGrpCat.{u + 1}

/-- Inverse-image cocone of finite locally constant abelian sheaves. -/
public abbrev addCommGrpCocone := @cocone AddCommGrpCat.{u + 1}

/-- Comparison from the filtered colimit of finite locally constant abelian sheaves. -/
public abbrev addCommGrpComparison := @comparison AddCommGrpCat.{u + 1}

/-- Mediating `Cat` morphism for finite locally constant abelian sheaves. -/
public abbrev addCommGrpDesc := @desc AddCommGrpCat.{u + 1}

/-- Cat-valued diagram of finite-type locally constant sheaves of modules. -/
public abbrev moduleDiagram {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ] :=
  @diagram (ModuleCat.{v} Λ)

/-- Inverse-image cocone of finite-type locally constant sheaves of modules. -/
public abbrev moduleCocone {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ] :=
  @cocone (ModuleCat.{v} Λ)

/-- Comparison from the filtered colimit of finite-type locally constant sheaves of modules. -/
public abbrev moduleComparison {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ] :=
  @comparison (ModuleCat.{v} Λ)

/-- Mediating `Cat` morphism for finite-type locally constant sheaves of modules. -/
public abbrev moduleDesc {Λ : Type v} [Ring Λ] [IsNoetherianRing Λ] :=
  @desc (ModuleCat.{v} Λ)

end AlgebraicGeometry.Scheme.Etale.FiniteLocallyConstant

end
