module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigStructureSheaf

/-! # Functorial morphisms of big étale ringed topoi -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition admits pointwise right Kan extensions of type-valued presheaves in
universe `u`. -/
instance map_op_hasPointwiseRightKanExtension_typeU (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type u) :
    (Over.map f).op.HasPointwiseRightKanExtension P :=
  fun U ↦
    let t := mkInitialOfLeftAdjoint (Over.map f).op (Over.mapPullbackAdj f).op U
    ⟨⟨⟨coneOfDiagramInitial t (StructuredArrow.proj U (Over.map f).op ⋙ P),
      limitOfDiagramInitial t (StructuredArrow.proj U (Over.map f).op ⋙ P)⟩⟩⟩

/-- Postcomposition admits pointwise right Kan extensions of ring-valued presheaves. -/
instance map_op_hasPointwiseRightKanExtension_ringCat (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ RingCat.{u}) :
    (Over.map f).op.HasPointwiseRightKanExtension P :=
  fun U ↦
    let t := mkInitialOfLeftAdjoint (Over.map f).op (Over.mapPullbackAdj f).op U
    ⟨⟨⟨coneOfDiagramInitial t (StructuredArrow.proj U (Over.map f).op ⋙ P),
      limitOfDiagramInitial t (StructuredArrow.proj U (Over.map f).op ⋙ P)⟩⟩⟩

/-- The forgetful functor on rings preserves the right Kan extensions used by `f_big`. -/
instance map_op_forgetRingCat_preservesRightKanExtensions (f : Y ⟶ X) :
    (forget RingCat.{u}).PreservesRightKanExtensions (Over.map f).op :=
  by
    intro P
    apply (config := { allowSynthFailures := true })
      Functor.preservesPointwiseRKEOfHasPointwiseAndPreservesPointwise
    intro U
    apply (config := { allowSynthFailures := true })
      Functor.preservesPointwiseRightKanExtensionAtOfPreservesLimit
    let t := mkInitialOfLeftAdjoint (Over.map f).op (Over.mapPullbackAdj f).op U
    exact @Functor.Initial.preservesLimit_of_comp _ _ _ _
      (Functor.fromPUnit.{0}
        (StructuredArrow.mk ((Over.mapPullbackAdj f).op.unit.app U) :
          StructuredArrow U (Over.map f).op))
      (Functor.initial_fromPUnit_of_isInitial t) _ _
      (StructuredArrow.proj U (Over.map f).op ⋙ P) _ _ (forget RingCat.{u})
      (by infer_instance)

/-- Inverse image of type-valued sheaves along `f_big` preserves finite limits. -/
instance mapInverseImage_typeU_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits
      ((Over.map f).sheafPushforwardContinuous (Type u)
        (overEtaleTopology Y) (overEtaleTopology X)) :=
  sorry

/-- Inverse image of ring sheaves on the big étale site is restriction along postcomposition. -/
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
  rfl

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
instance sharp_isIso (f : Y ⟶ X) : IsIso (sharp f) :=
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

/-- The canonical inverse-image structure map of a big étale morphism is invertible. -/
instance ringedHom_structureMap_isIso (f : Y ⟶ X) :
    IsIso (ringedHom f).structureMap :=
  sorry

/-- Big étale ringed morphisms respect composition up to canonical isomorphism. -/
def ringedHomCompIso {Z : AlgebraicSpace S} (f : Y ⟶ X) (g : Z ⟶ Y) :
    TwoIso.{u + 1, u + 1, u + 1, u + 1, u}
      (comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u}
        (ringedHom g) (ringedHom f)) (ringedHom (g ≫ f)) where
  homIso :=
    Adjunction.rightAdjointUniq
      (((ringedMorphismOfTopoi f).adjunction.comp
        (ringedMorphismOfTopoi g).adjunction).ofNatIsoLeft
        (Functor.sheafPushforwardContinuousComp' (Over.mapComp g f).symm (Type u)
          (overEtaleTopology Z) (overEtaleTopology Y) (overEtaleTopology X)))
      (ringedMorphismOfTopoi (g ≫ f)).adjunction
  comm := by sorry

/-- The big étale ringed morphism of an identity is canonically the identity. -/
def ringedHomIdIso (X : AlgebraicSpace S) :
    TwoIso.{u + 1, u + 1, u + 1, u + 1, u}
      (ringedHom (𝟙 X)) (RingedSite.ToposHom.id (ringedSite X)) where
  homIso :=
    Adjunction.rightAdjointUniq
      ((ringedMorphismOfTopoi (𝟙 X)).adjunction.ofNatIsoLeft
        (Functor.sheafPushforwardContinuousId' (Over.mapId X) (Type u)
          (overEtaleTopology X)))
      Adjunction.id
  comm := by sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Big
