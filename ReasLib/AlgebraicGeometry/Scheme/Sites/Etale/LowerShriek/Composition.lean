module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.CategoryTheory.Subobject.FactorThru

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Small-étale base change along `g` then `f` is naturally isomorphic to base
change along `f ≫ g`. -/
def smallEtalePullbackCompIso :
    smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
  (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm

/-- Iterated direct image of abelian small-étale sheaves is naturally isomorphic
to direct image along the composite morphism. -/
def etaleAbelianPushforwardCompIso :
    (smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology ⋙
      (smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Y.smallEtaleTopology ≅
      (smallEtalePullback (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology X.smallEtaleTopology :=
  sheafPushforwardContinuousComp' (smallEtalePullbackCompIso f g) AddCommGrpCat.{u}
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyOfFiniteType g]

/-- The canonical inclusion of iterated compact-support direct image into
ordinary direct image along the composite morphism. -/
def etaleLowerShriekCompι :
    etaleLowerShriek f ⋙ etaleLowerShriek g ⟶
      (smallEtalePullback (f ≫ g)).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology X.smallEtaleTopology :=
  whiskerLeft (etaleLowerShriek f) (etaleLowerShriekι g) ≫
    whiskerRight (etaleLowerShriekι f)
      ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Y.smallEtaleTopology) ≫
    (etaleAbelianPushforwardCompIso f g).hom

/-- On a sheaf, the composite compact-support inclusion is the composition of
the two compact-support inclusions and the ordinary-pushforward comparison. -/
theorem etaleLowerShriekCompι_app (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekCompι f g).app F =
      (etaleLowerShriekι g).app ((etaleLowerShriek f).obj F) ≫
        ((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
          Z.smallEtaleTopology Y.smallEtaleTopology).map ((etaleLowerShriekι f).app F) ≫
        (etaleAbelianPushforwardCompIso f g).hom.app F := sorry

/-- The image of iterated compact-support sections in the sections of ordinary
direct image along the composite morphism. -/
def etaleLowerShriekCompSections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (W : Z.Etale) :
    AddSubgroup (F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))) :=
  AddSubgroup.map
    (AddCommGrpCat.Hom.hom
      (((etaleLowerShriekCompι f g).app F).hom.app (op W))) ⊤

/-- A section belongs to the iterated compact-support image precisely when it
is the image of a compact-support section of the first direct image. -/
theorem mem_etaleLowerShriekCompSections_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback (f ≫ g)).obj W))) :
    σ ∈ etaleLowerShriekCompSections f g F W ↔
      ∃ τ : compactSupportSections g ((etaleLowerShriek f).obj F) W,
        ((etaleLowerShriekCompι f g).app F).hom.app (op W) τ = σ := sorry

/-- For composable separated locally finite-type scheme morphisms, sections
with proper support along the composite equal the iterated compact-support
sections inside the ordinary direct image. -/
theorem etaleLowerShriek_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections (f ≫ g) F W =
      etaleLowerShriekCompSections f g F W := sorry

/-- The pushforward comparison `g_! ∘ f_! ⟶ (f ≫ g)_*` factors through the
compact-support inclusion `(f ≫ g)_! ⟶ (f ≫ g)_*`. -/
theorem etaleLowerShriekComp_factors :
    MonoOver.Factors (MonoOver.mk (etaleLowerShriekι (f ≫ g)))
      (etaleLowerShriekCompι f g) :=
  sorry

/-- The ordinary composition comparison sends iterated compact-support sections
to sections with proper support along the composite. -/
theorem etaleLowerShriekCompSectionMap_mem
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : compactSupportSections g ((etaleLowerShriek f).obj F) W) :
    ((etaleLowerShriekCompι f g).app F).hom.app (op W) σ ∈
      compactSupportSections (f ≫ g) F W :=
  sorry

/-- The ordinary composition comparison restricted to compact-support sections. -/
def etaleLowerShriekCompSectionMap
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections g ((etaleLowerShriek f).obj F) W →+
      compactSupportSections (f ≫ g) F W :=
  ((((etaleLowerShriekCompι f g).app F).hom.app (op W)).hom).codRestrict
    (compactSupportSections (f ≫ g) F W)
    (etaleLowerShriekCompSectionMap_mem f g F W)

/-- The compact-support composition section maps commute with restriction. -/
theorem etaleLowerShriekComp_sections_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V W : Z.Etaleᵒᵖ} (a : V ⟶ W) :
    (etaleLowerShriekPresheaf g ((etaleLowerShriek f).obj F)).map a ≫
        AddCommGrpCat.ofHom (etaleLowerShriekCompSectionMap f g F W.unop) =
      AddCommGrpCat.ofHom (etaleLowerShriekCompSectionMap f g F V.unop) ≫
        (etaleLowerShriekPresheaf (f ≫ g) F).map a :=
  sorry

/-- The compact-support composition comparison at an abelian étale sheaf. -/
def etaleLowerShriekComp_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriek g).obj ((etaleLowerShriek f).obj F) ⟶
      (etaleLowerShriek (f ≫ g)).obj F :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom
        (etaleLowerShriekCompSectionMap f g F W.unop)
      naturality := fun _ _ a ↦ etaleLowerShriekComp_sections_naturality f g F a }

/-- The compact-support composition comparison is natural in the coefficient sheaf. -/
theorem etaleLowerShriekComp_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    (etaleLowerShriek f ⋙ etaleLowerShriek g).map α ≫ etaleLowerShriekComp_app f g G =
      etaleLowerShriekComp_app f g F ≫ (etaleLowerShriek (f ≫ g)).map α :=
  sorry

/-- The canonical comparison `f_! ⋙ g_! ⟶ (f ≫ g)_!` defined by restricting
the ordinary-pushforward comparison to compact-support sections. -/
def etaleLowerShriekComp :
    etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleLowerShriek (f ≫ g) where
  app := etaleLowerShriekComp_app f g
  naturality := fun _ _ α ↦ etaleLowerShriekComp_naturality f g α

/-- The comparison fills the triangle with the compact-support inclusion of
`(f ≫ g)_!`. -/
theorem etaleLowerShriekComp_ι :
    etaleLowerShriekComp f g ≫ etaleLowerShriekι (f ≫ g) =
      etaleLowerShriekCompι f g :=
  sorry

/-- Any morphism making the compact-support triangle commute equals the
canonical comparison. -/
theorem etaleLowerShriekComp_lift_unique
    (α : etaleLowerShriek f ⋙ etaleLowerShriek g ⟶ etaleLowerShriek (f ≫ g))
    (hα : α ≫ etaleLowerShriekι (f ≫ g) = etaleLowerShriekCompι f g) :
    α = etaleLowerShriekComp f g :=
  sorry

/-- Inverse ordinary-pushforward transport of a section with proper support
along the composite, viewed as a section on the iterated pullback. -/
def etaleLowerShriekCompInvAmbient
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections (f ≫ g) F W →+
      F.obj.obj (op ((smallEtalePullback f).obj ((smallEtalePullback g).obj W))) :=
  ((((etaleAbelianPushforwardCompIso f g).inv.app F).hom.app (op W)).hom).comp
    (compactSupportSections (f ≫ g) F W).subtype

/-- Inverse composition transport of a compact-support section has proper
support over the intermediate base. -/
theorem etaleLowerShriekCompInvAmbient_mem
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : compactSupportSections (f ≫ g) F W) :
    etaleLowerShriekCompInvAmbient f g F W σ ∈
      compactSupportSections f F ((smallEtalePullback g).obj W) :=
  sorry

/-- Inverse composition transport restricted to the compact-support direct
image along the first morphism. -/
def etaleLowerShriekCompInvInner
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections (f ≫ g) F W →+
      compactSupportSections f F ((smallEtalePullback g).obj W) :=
  (etaleLowerShriekCompInvAmbient f g F W).codRestrict
    (compactSupportSections f F ((smallEtalePullback g).obj W))
    (etaleLowerShriekCompInvAmbient_mem f g F W)

/-- Inverse composition transport into the first compact-support direct image
has proper support over the final base. -/
theorem etaleLowerShriekCompInvInner_mem
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale)
    (σ : compactSupportSections (f ≫ g) F W) :
    etaleLowerShriekCompInvInner f g F W σ ∈
      compactSupportSections g ((etaleLowerShriek f).obj F) W :=
  sorry

/-- The inverse ordinary composition map restricted through both stages of
compact-support direct image. -/
def etaleLowerShriekCompInvSectionMap
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections (f ≫ g) F W →+
      compactSupportSections g ((etaleLowerShriek f).obj F) W :=
  (etaleLowerShriekCompInvInner f g F W).codRestrict
    (compactSupportSections g ((etaleLowerShriek f).obj F) W)
    (etaleLowerShriekCompInvInner_mem f g F W)

/-- The inverse compact-support composition section maps commute with restriction. -/
theorem etaleLowerShriekCompInv_sections_naturality
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V W : Z.Etaleᵒᵖ} (a : V ⟶ W) :
    (etaleLowerShriekPresheaf (f ≫ g) F).map a ≫
        AddCommGrpCat.ofHom (etaleLowerShriekCompInvSectionMap f g F W.unop) =
      AddCommGrpCat.ofHom (etaleLowerShriekCompInvSectionMap f g F V.unop) ≫
        (etaleLowerShriekPresheaf g ((etaleLowerShriek f).obj F)).map a :=
  sorry

/-- The inverse compact-support composition comparison at an abelian étale sheaf. -/
def etaleLowerShriekCompInv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriek (f ≫ g)).obj F ⟶
      (etaleLowerShriek g).obj ((etaleLowerShriek f).obj F) :=
  ObjectProperty.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom
        (etaleLowerShriekCompInvSectionMap f g F W.unop)
      naturality := fun _ _ a ↦ etaleLowerShriekCompInv_sections_naturality f g F a }

/-- The inverse compact-support composition comparison is natural in the
coefficient sheaf. -/
theorem etaleLowerShriekCompInv_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (α : F ⟶ G) :
    (etaleLowerShriek (f ≫ g)).map α ≫ etaleLowerShriekCompInv_app f g G =
      etaleLowerShriekCompInv_app f g F ≫ (etaleLowerShriek f ⋙ etaleLowerShriek g).map α :=
  sorry

/-- The inverse composition comparison on compact-support direct images,
defined by inverse ordinary-pushforward transport and subgroup restrictions. -/
def etaleLowerShriekCompInv :
    etaleLowerShriek (f ≫ g) ⟶ etaleLowerShriek f ⋙ etaleLowerShriek g where
  app := etaleLowerShriekCompInv_app f g
  naturality := fun _ _ α ↦ etaleLowerShriekCompInv_naturality f g α

/-- Composition comparison followed by inverse comparison is the identity. -/
theorem etaleLowerShriekComp_hom_inv_id :
    etaleLowerShriekComp f g ≫ etaleLowerShriekCompInv f g =
      𝟙 (etaleLowerShriek f ⋙ etaleLowerShriek g) :=
  sorry

/-- Inverse composition comparison followed by comparison is the identity. -/
theorem etaleLowerShriekComp_inv_hom_id :
    etaleLowerShriekCompInv f g ≫ etaleLowerShriekComp f g =
      𝟙 (etaleLowerShriek (f ≫ g)) :=
  sorry

/-- The comparison `f_! ⋙ g_! ⟶ (f ≫ g)_!` is an isomorphism. -/
instance etaleLowerShriekComp_isIso : IsIso (etaleLowerShriekComp f g) where
  out := ⟨etaleLowerShriekCompInv f g, etaleLowerShriekComp_hom_inv_id f g,
    etaleLowerShriekComp_inv_hom_id f g⟩

/-- The functor isomorphism `f_! ⋙ g_! ≅ (f ≫ g)_!`. -/
def etaleLowerShriekCompIso :
    etaleLowerShriek f ⋙ etaleLowerShriek g ≅ etaleLowerShriek (f ≫ g) where
  hom := etaleLowerShriekComp f g
  inv := etaleLowerShriekCompInv f g
  hom_inv_id := etaleLowerShriekComp_hom_inv_id f g
  inv_hom_id := etaleLowerShriekComp_inv_hom_id f g

/-- The forward map of `etaleLowerShriekCompIso` is the compact-support
composition comparison. -/
theorem etaleLowerShriekCompIso_hom :
    (etaleLowerShriekCompIso f g).hom = etaleLowerShriekComp f g :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
