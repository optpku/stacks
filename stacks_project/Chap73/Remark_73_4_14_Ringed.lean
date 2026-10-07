module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import stacks_project.Chap66.Lemma_66_21_3
public import stacks_project.Chap73.Lemma_73_4_8_Identity
public import stacks_project.Chap73.Lemma_73_4_10_Big
public import stacks_project.Chap73.Remark_73_4_14_StructureSheaf

/-!
# Ringed upgrades of spaces-étale and big étale morphisms

The morphisms `i_f`, `π_X`, `i_X`, and `f_big` of Lemmas 73.4.7, 73.4.8, and 73.4.11
upgrade to morphisms of ringed topoi (respectively sites). Inverse image along
relocalization and along `Over.map` is restriction, so the source-facing comparisons
are objectwise identifications of global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Spaces-étale relocalization along `f` is a morphism of sites. -/
instance relocalizationFunctor_isMorphismOfSites (f : Y ⟶ X) :
    IsMorphismOfSites (spacesEtaleTopology Y) (overEtaleTopology X)
      (relocalizationFunctor f) :=
  sorry

/-- Inverse image of ring sheaves along `i_f`, i.e. restriction along relocalization. -/
abbrev relocalizationPushforward (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) RingCat.{u} ⥤ Sheaf (spacesEtaleTopology Y) RingCat.{u} :=
  (relocalizationFunctor f).sheafPushforwardContinuous RingCat.{u}
    (spacesEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image along `i_f` evaluates to global sections of the relocalized object. -/
theorem relocalizationPushforward_obj_obj (f : Y ⟶ X) (U : spacesEtaleSite Y) :
    ((relocalizationPushforward f).obj (Big.structureSheaf X)).obj.obj (op U) =
      Big.gamma ((relocalizationFunctor f).obj U).left :=
  rfl

/-- Inverse image of type-valued sheaves along `i_f` preserves finite limits. -/
instance relocalizationInverseImage_typeU_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits
      ((relocalizationFunctor f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (overEtaleTopology X)) :=
  sorry

/-- Type-`u` morphism of topoi `i_f : Sh(Y_spaces,étale) ⟶ Sh((Spaces/X)_étale)`. -/
def relocalizationMorphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((relocalizationFunctor f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (overEtaleTopology X))
  pushforward :=
    (relocalizationFunctor f).sheafPushforwardCocontinuous (Type u)
      (spacesEtaleTopology Y) (overEtaleTopology X)
  adjunction :=
    (relocalizationFunctor f).sheafAdjunctionCocontinuous (Type u)
      (spacesEtaleTopology Y) (overEtaleTopology X)

/-- The underlying inverse image of `relocalizationMorphismOfTopoi f` is restriction along
relocalization. -/
theorem relocalizationMorphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (relocalizationMorphismOfTopoi f).inverseImage =
      (relocalizationFunctor f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (overEtaleTopology X) :=
  sorry

/-- Direct-image comparison `𝒪_Y ⟶ i_f⁻¹ 𝒪` on spaces-étale sites, objectwise
`𝒪_Y(U) ⟶ Γ(U, 𝒪_U)`. -/
def relocalizationStructureSheafMap (f : Y ⟶ X) :
    spacesStructureSheaf Y ⟶ (relocalizationPushforward f).obj (Big.structureSheaf X) :=
  InducedCategory.homMk
    { app := fun U => Big.spacesStructureToGamma U.unop
      naturality := fun _ _ _ => sorry }

/-- Component of `relocalizationStructureSheafMap f` at `U/Y`. -/
theorem relocalizationStructureSheafMap_app (f : Y ⟶ X) (U : spacesEtaleSite Y) :
    (relocalizationStructureSheafMap f).hom.app (op U) = Big.spacesStructureToGamma U :=
  rfl

/-- The comparison `𝒪_Y ⟶ i_f⁻¹ 𝒪` is an isomorphism of ring sheaves; its inverse is the
source map `i_f^♯ : i_f⁻¹ 𝒪 ⟶ 𝒪_Y`. -/
theorem relocalizationStructureSheafMap_isIso (f : Y ⟶ X) :
    IsIso (relocalizationStructureSheafMap f) :=
  sorry

/-- Identity-base relocalization as a morphism of ringed sites, i.e. `π_X`. -/
def siteHom (X : AlgebraicSpace S) :
    RingedSite.Hom (Big.ringedSite X) (spacesRingedSite X) where
  base := relocalizationFunctor (𝟙 X)
  structureSheafMap := relocalizationStructureSheafMap (𝟙 X)

/-- The base functor of `siteHom X` is identity-base relocalization. -/
theorem siteHom_base (X : AlgebraicSpace S) :
    (siteHom X).base = relocalizationFunctor (𝟙 X) :=
  rfl

/-- Direct-image structure map of `π_X`, i.e. `π_X^♯ : 𝒪_X ⟶ π_{X,*} 𝒪`. -/
def siteSharp (X : AlgebraicSpace S) :
    spacesStructureSheaf X ⟶ (relocalizationPushforward (𝟙 X)).obj (Big.structureSheaf X) :=
  (siteHom X).structureSheafMap

/-- `siteSharp X` is the structure-sheaf map of `siteHom X`. -/
theorem siteSharp_eq (X : AlgebraicSpace S) :
    siteSharp X = (siteHom X).structureSheafMap :=
  rfl

/-- On `U/X`, `π_X^♯` compares `𝒪_X(U)` with `(π_{X,*} 𝒪)(U) = 𝒪(U)`. -/
theorem siteSharp_app (X : AlgebraicSpace S) (U : spacesEtaleSite X) :
    (siteSharp X).hom.app (op U) = Big.spacesStructureToGamma U :=
  rfl

/-- `i_X` is the special case of `i_f` with `f = 𝟙 X`. -/
def identityRelocalization (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (spacesEtaleTopology X) :=
  relocalizationMorphismOfTopoi (𝟙 X)

/-- `identityRelocalization X` is `relocalizationMorphismOfTopoi` along `𝟙 X`. -/
theorem identityRelocalization_eq (X : AlgebraicSpace S) :
    identityRelocalization X = relocalizationMorphismOfTopoi (𝟙 X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition on big étale slices is a morphism of sites. -/
instance map_isMorphismOfSites (f : Y ⟶ X) :
    IsMorphismOfSites (overEtaleTopology Y) (overEtaleTopology X) (Over.map f) :=
  sorry

/-- Postcomposition on big étale slices is cocontinuous. -/
instance map_isCocontinuous (f : Y ⟶ X) :
    (Over.map f).IsCocontinuous (overEtaleTopology Y) (overEtaleTopology X) :=
  sorry

/-- Postcomposition admits pointwise right Kan extensions of type-valued presheaves in
universe `u`. -/
instance map_op_hasPointwiseRightKanExtension_typeU (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type u) :
    (Over.map f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Postcomposition admits pointwise right Kan extensions of ring-valued presheaves. -/
instance map_op_hasPointwiseRightKanExtension_ringCat (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ RingCat.{u}) :
    (Over.map f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The forgetful functor on rings preserves the right Kan extensions used by `f_big`. -/
instance map_op_forgetRingCat_preservesRightKanExtensions (f : Y ⟶ X) :
    (forget RingCat.{u}).PreservesRightKanExtensions (Over.map f).op :=
  sorry

/-- Inverse image of type-valued sheaves along `f_big` preserves finite limits. -/
instance mapInverseImage_typeU_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits
      ((Over.map f).sheafPushforwardContinuous (Type u)
        (overEtaleTopology Y) (overEtaleTopology X)) :=
  sorry

/-- Direct image of the big étale structure sheaf along postcomposition. -/
abbrev mapPushforward (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) RingCat.{u} ⥤ Sheaf (overEtaleTopology Y) RingCat.{u} :=
  (Over.map f).sheafPushforwardContinuous RingCat.{u}
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Restriction of `𝒪_X` along `Over.map f` is `Γ(U, 𝒪_U)` on objects. -/
theorem mapPushforward_obj_obj (f : Y ⟶ X) (U : Over Y) :
    ((mapPushforward f).obj (structureSheaf X)).obj.obj (op U) = gamma U.left :=
  rfl

/-- Cocontinuous direct image of ring sheaves along `f_big`. -/
abbrev mapDirectImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) RingCat.{u} ⥤ Sheaf (overEtaleTopology X) RingCat.{u} :=
  (Over.map f).sheafPushforwardCocontinuous RingCat.{u}
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Type-`u` morphism of topoi `f_big : Sh((Spaces/Y)_étale) ⟶ Sh((Spaces/X)_étale)`. -/
def ringedMorphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (overEtaleTopology X) (overEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((Over.map f).sheafPushforwardContinuous (Type u)
        (overEtaleTopology Y) (overEtaleTopology X))
  pushforward :=
    (Over.map f).sheafPushforwardCocontinuous (Type u)
      (overEtaleTopology Y) (overEtaleTopology X)
  adjunction :=
    (Over.map f).sheafAdjunctionCocontinuous (Type u)
      (overEtaleTopology Y) (overEtaleTopology X)

/-- The direct image of `ringedMorphismOfTopoi f` is cocontinuous sheaf pushforward
along `Over.map f`. -/
theorem ringedMorphismOfTopoi_pushforward (f : Y ⟶ X) :
    (ringedMorphismOfTopoi f).pushforward =
      (Over.map f).sheafPushforwardCocontinuous (Type u)
        (overEtaleTopology Y) (overEtaleTopology X) :=
  rfl

/-- The inverse image of `ringedMorphismOfTopoi f` is restriction along `Over.map f`. -/
theorem ringedMorphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (ringedMorphismOfTopoi f).inverseImage =
      (Over.map f).sheafPushforwardContinuous (Type u)
        (overEtaleTopology Y) (overEtaleTopology X) :=
  sorry

/-- The inverse-image map `f_big^♯ : f_big⁻¹ 𝒪_X ⟶ 𝒪_Y`, objectwise the identity on
`Γ(U, 𝒪_U)`. -/
def sharp (f : Y ⟶ X) :
    (mapPushforward f).obj (structureSheaf X) ⟶ structureSheaf Y :=
  InducedCategory.homMk
    { app := fun U => 𝟙 (gamma U.unop.left)
      naturality := fun _ _ _ => sorry }

/-- `f_big^♯` is objectwise the identity of `Γ(U, 𝒪_U)`. -/
theorem sharp_app (f : Y ⟶ X) (U : Over Y) :
    (sharp f).hom.app (op U) = 𝟙 (gamma U.left) :=
  rfl

/-- `f_big^♯` is an isomorphism of ring sheaves on `(Spaces/Y)_étale`. -/
theorem sharp_isIso (f : Y ⟶ X) : IsIso (sharp f) :=
  sorry

/-- Direct-image form of `f_big^♯`, the adjunct of the objectwise identity on `Γ`. -/
def ringedDirectStructureMap (f : Y ⟶ X) :
    structureSheaf X ⟶ (mapDirectImage f).obj (structureSheaf Y) :=
  ((Over.map f).sheafAdjunctionCocontinuous RingCat.{u}
      (overEtaleTopology Y) (overEtaleTopology X)).homEquiv _ _ (sharp f)

/-- Coefficient-forgetful comparison for cocontinuous pushforward along `Over.map f`. -/
def ringedForgetIso (f : Y ⟶ X) :
    mapDirectImage f ⋙ sheafCompose (overEtaleTopology X) (forget RingCat.{u}) ≅
      sheafCompose (overEtaleTopology Y) (forget RingCat.{u}) ⋙
        (ringedMorphismOfTopoi f).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (Over.map f) (forget RingCat.{u}) (overEtaleTopology Y) (overEtaleTopology X)

/-- `ringedForgetIso f` is the canonical cocontinuous coefficient comparison. -/
theorem ringedForgetIso_eq (f : Y ⟶ X) :
    ringedForgetIso f =
      Functor.sheafPushforwardCocontinuous.compSheafComposeIso
        (Over.map f) (forget RingCat.{u}) (overEtaleTopology Y) (overEtaleTopology X) :=
  rfl

/-- Direct-image ring compatibility of `f_big`. -/
theorem ringedDirectStructureMap_isRingCompatible (f : Y ⟶ X) :
    @Direct.IsRingCompatible (ringedSite Y) (ringedSite X) _ _
      (ringedMorphismOfTopoi f) (mapDirectImage f) (ringedForgetIso f)
      (ringedDirectStructureMap f) :=
  sorry

/-- The morphism of ringed topoi `f_big : ((Spaces/Y)_étale, 𝒪_Y) ⟶ ((Spaces/X)_étale, 𝒪_X)`. -/
def ringedHom (f : Y ⟶ X) : RingedSite.ToposHom (ringedSite Y) (ringedSite X) :=
  @ofDirectImage (ringedSite Y) (ringedSite X) _ _ (ringedMorphismOfTopoi f)
    (mapDirectImage f) (ringedForgetIso f) (ringedDirectStructureMap f)
    (ringedDirectStructureMap_isRingCompatible f)

/-- The underlying topos morphism of `ringedHom f` is `ringedMorphismOfTopoi f`. -/
theorem ringedHom_toTopos (f : Y ⟶ X) :
    (ringedHom f).toTopos = ringedMorphismOfTopoi f :=
  rfl

/-- `ringedHom` is functorial in the morphism of algebraic spaces. -/
theorem ringedHom_comp {Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y) :
    RingedSite.ToposHom.comp (ringedHom g) (ringedHom f) = ringedHom (g ≫ f) :=
  sorry

/-- `ringedHom` sends identities to identity morphisms of ringed topoi. -/
theorem ringedHom_id (X : AlgebraicSpace S) :
    ringedHom (𝟙 X) = RingedSite.ToposHom.id (ringedSite X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
