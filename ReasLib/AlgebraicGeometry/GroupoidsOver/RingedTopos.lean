module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.Pushforward.SmallSectionsRing

@[expose] public section
open AlgebraicGeometry CategoryTheory Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory MorphismOfTopoiIn
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The total functor of a 1-morphism is continuous for associated `τ`-topologies. -/
instance toFunctor_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f).IsContinuous (X.associatedTopology τ) (Y.associatedTopology τ) :=
  sorry

/-- The composite `toFunctor f ⋙ Y.p` is continuous from `X_τ` to the big `τ`-site of `S`. -/
instance toFunctor_comp_p_isContinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f ⋙ Y.p).IsContinuous (X.associatedTopology τ) (τ.overTopology S) :=
  Functor.isContinuous_comp (toFunctor f) Y.p
    (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)

/-- Ring-valued sheaves on an associated `τ`-topology compose with `forget RingCat`. -/
instance associatedTopology_hasSheafCompose (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose (forget RingCat.{u}) :=
  sorry

/-- The canonical identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of associated `τ`-structure sheaves,
obtained from the commuting triangle `toFunctor f ⋙ Y.p = X.p`. -/
def associatedStructureSheafInverseImageIso {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
      (associatedStructureSheaf Y τ) ≅ associatedStructureSheaf X τ :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
      (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)).app
    (StandardTopology.Big.structureSheaf τ S)

/-- `associatedStructureSheafInverseImageIso` is the continuous-pushforward comparison
along `comm f`. -/
theorem associatedStructureSheafInverseImageIso_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    associatedStructureSheafInverseImageIso f τ =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (X.associatedTopology τ) (Y.associatedTopology τ) (τ.overTopology S)).app
        (StandardTopology.Big.structureSheaf τ S) :=
  rfl

/-- At an object `x` of `X`, the identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` evaluates as
`𝒪_Y((toFunctor f).obj x) = 𝒪_X(x)`. -/
theorem associatedStructureSheafInverseImageIso_app {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) (x : X.total) :
    (associatedStructureSheaf Y τ).obj.obj (op ((toFunctor f).obj x)) =
      (associatedStructureSheaf X τ).obj.obj (op x) :=
  sorry

/-- The total functor is cocontinuous for the topologies of the associated `τ`-ringed
sites. -/
instance toFunctor_isCocontinuous {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (toFunctor f).IsCocontinuous
      (X.associatedTopology τ) (Y.associatedTopology τ) :=
  sorry

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` as a morphism of underlying ring presheaves. -/
def associatedStructureSheafInverseImagePresheafHom {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    (toFunctor f).op ⋙ (associatedRingedSite Y τ).structureSheaf.obj ⟶
      (associatedRingedSite X τ).structureSheaf.obj :=
  (associatedStructureSheafInverseImageIso f τ).hom.hom

/-- `associatedStructureSheafInverseImagePresheafHom` is the underlying presheaf morphism
of `associatedStructureSheafInverseImageIso`. -/
theorem associatedStructureSheafInverseImagePresheafHom_eq {X Y : GroupoidsOver S}
    (f : X ⟶ Y) (τ : StandardTopology) :
    associatedStructureSheafInverseImagePresheafHom f τ =
      (associatedStructureSheafInverseImageIso f τ).hom.hom :=
  rfl

/-- Compatible sections of actual type-valued sheaves along a fibred-groupoid morphism
are small in the coefficient universe. -/
class HasSmallAssociatedTypeSections {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) : Prop where
  /-- Each sheaf-section diagram has a small type of compatible sections. -/
  small : ∀ F : Sheaf (X.associatedTopology τ) (Type u), ∀ Z : Y.totalᵒᵖ,
    Small.{u} (StructuredArrow.proj Z (toFunctor f).op ⋙ F.obj).sections

/-- The section-size condition supplies smallness of every actual sheaf diagram. -/
instance associatedTypeSections_small {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) [h : HasSmallAssociatedTypeSections f τ] :
    ∀ F : Sheaf (X.associatedTopology τ) (Type u), ∀ Z : Y.totalᵒᵖ,
      Small.{u} (StructuredArrow.proj Z (toFunctor f).op ⋙ F.obj).sections :=
  h.small

/-- Right Kan extensions of all presheaves imply the section-size condition for sheaves. -/
instance hasSmallAssociatedTypeSections_of_hasPointwiseRightKanExtension
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P] :
    HasSmallAssociatedTypeSections f τ where
  small F Z := (Limits.Types.hasLimit_iff_small_sections
    (StructuredArrow.proj Z (toFunctor f).op ⋙ F.obj)).mp inferInstance

section SmallSections
variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSmallAssociatedTypeSections f τ]

/-- The direct structure map is the transpose of the canonical projection comparison. -/
def associatedRingedToposHom_directStructureMap :
    (associatedRingedSite Y τ).structureSheaf ⟶
      ((toFunctor f).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
        (X.associatedTopology τ) (Y.associatedTopology τ)).obj
        (associatedRingedSite X τ).structureSheaf :=
  ((toFunctor f).sheafPushforwardRingOfSmallSectionsAdjunction.{u + 1, u, u + 1, u, u}
    (X.associatedTopology τ) (Y.associatedTopology τ)).homEquiv _ _
    (associatedStructureSheafInverseImageIso f τ).hom

/-- The transposed projection comparison preserves the internal-ring operations. -/
theorem associatedRingedToposHom_isRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (associatedRingedSite X τ) (associatedRingedSite Y τ) inferInstance inferInstance
      ((toFunctor f).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
        (X.associatedTopology τ) (Y.associatedTopology τ))
      ((toFunctor f).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
        (X.associatedTopology τ) (Y.associatedTopology τ))
      ((toFunctor f).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u}
        (X.associatedTopology τ) (Y.associatedTopology τ))
      (associatedRingedToposHom_directStructureMap f τ) := sorry

/-- A morphism of fibred groupoids induces a morphism of associated ringed topoi
when its actual type-valued sheaf sections are small. -/
def associatedRingedToposHom :
    RingedSite.ToposHom (associatedRingedSite X τ) (associatedRingedSite Y τ) :=
  RingedSite.ToposHom.ofDirectImage.{u + 1, u, u + 1, u, u}
    ((toFunctor f).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
      (X.associatedTopology τ) (Y.associatedTopology τ))
    ((toFunctor f).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
      (X.associatedTopology τ) (Y.associatedTopology τ))
    ((toFunctor f).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u}
      (X.associatedTopology τ) (Y.associatedTopology τ))
    (associatedRingedToposHom_directStructureMap f τ)
    (associatedRingedToposHom_isRingCompatible f τ)

/-- The underlying geometric morphism uses continuous inverse image and small sheaf sections. -/
theorem associatedRingedToposHom_toTopos :
    (associatedRingedToposHom f τ).toTopos =
      (toFunctor f).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
        (X.associatedTopology τ) (Y.associatedTopology τ) := rfl

/-- The inverse structure map is reconstructed from the transposed projection comparison. -/
theorem associatedRingedToposHom_structureMap :
    (associatedRingedToposHom f τ).structureMap =
      @RingedSite.ToposHom.Direct.inverseStructureMap.{u + 1, u, u + 1, u, u}
        (associatedRingedSite X τ) (associatedRingedSite Y τ) inferInstance inferInstance
        ((toFunctor f).morphismOfTopoiOfSmallSheafSections.{u + 1, u, u + 1, u, u}
          (X.associatedTopology τ) (Y.associatedTopology τ))
        ((toFunctor f).sheafPushforwardRingOfSmallSections.{u + 1, u, u + 1, u, u}
          (X.associatedTopology τ) (Y.associatedTopology τ))
        ((toFunctor f).sheafPushforwardRingOfSmallSectionsForgetIso.{u + 1, u, u + 1, u, u}
          (X.associatedTopology τ) (Y.associatedTopology τ))
        (associatedRingedToposHom_directStructureMap f τ)
        (associatedRingedToposHom_isRingCompatible f τ) := rfl

/-- The canonical inverse-image structure map of associated ringed topoi is invertible. -/
theorem associatedRingedToposHom_structureMap_isIso :
    IsIso (associatedRingedToposHom f τ).structureMap := sorry

end SmallSections

end AlgebraicGeometry.GroupoidsOver
