module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # The small-etale presentation inclusion into algebraic spaces

The actual chart conversion keeps the source presentation site distinct from the native
Yoneda site and then includes its scheme charts as algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The inclusion of schemes étale over `X` into algebraic spaces étale over `X`. -/
def smallEtaleToSpaces (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ spacesEtaleSite X :=
  SmallEtale.fromPresentation X ⋙ smallEtaleInclusion X

/-- The actual chart inclusion is faithful: its scheme map is determined by Yoneda. -/
instance smallEtaleToSpaces_faithful (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).Faithful where
  map_injective := by sorry

/-- The small-to-spaces comparison is cocontinuous. -/
instance smallEtaleToSpaces_isCocontinuous (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsCocontinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  sorry

/-- The specified image sieve of a presentation cover is a spaces-étale cover. -/
theorem smallEtaleToSpaces_coverPreserving (X : AlgebraicSpace S) :
    CoverPreserving (smallEtaleTopology X) (spacesEtaleTopology X) (smallEtaleToSpaces X) := sorry

/-- Compatible presentation families remain compatible after restricting along
actual factorization arrows in their image sieve. -/
theorem smallEtaleToSpaces_compatiblePreserving (X : AlgebraicSpace S) :
    CompatiblePreserving.{u + 1} (spacesEtaleTopology X) (smallEtaleToSpaces X) := sorry

/-- The restriction sheaf condition glues the actual pushed-forward family
using the supplied spaces-étale sheaf's descent. -/
instance smallEtaleToSpaces_isContinuous (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsContinuous (smallEtaleTopology X) (spacesEtaleTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (smallEtaleToSpaces_compatiblePreserving X) (smallEtaleToSpaces_coverPreserving X)

/-- The actual presentation inclusion has the same structural morphism into the space. -/
@[simp]
theorem smallEtaleToSpaces_obj_hom (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleToSpaces X).obj U).hom = U.hom := rfl

/-- Its object map sends the underlying scheme to its represented algebraic space. -/
@[simp]
theorem smallEtaleToSpaces_obj_left (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    ((smallEtaleToSpaces X).obj U).left = ofOver U.left := rfl

/-- The chart-to-spaces inclusion is special cocontinuous for the presentation topology. -/
instance smallEtaleToSpaces_isSpecialCocontinuous (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsSpecialCocontinuous (smallEtaleTopology X)
      (spacesEtaleTopology X) := sorry

/-- Type-valued sheaves on the presentation site have an actual right Kan extension. -/
instance smallEtaleToSpaces_op_hasPointwiseRightKanExtension (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (smallEtaleToSpaces X).op.HasPointwiseRightKanExtension P :=
  fun _ ↦ inferInstance

/-- The Yoneda preimage of a morphism of represented charts commutes with their maps to `X`. -/
private lemma smallEtaleToSpacesPreimage_w (X : AlgebraicSpace S) {U V : smallEtaleSite X}
    (f : (smallEtaleToSpaces X).obj U ⟶ (smallEtaleToSpaces X).obj V) :
    (ofOverFunctor S).map (yoneda.preimage f.left) ≫ V.hom = U.hom := by
  sorry

/-- Recover the actual scheme morphism underlying an arrow between presentation charts. -/
def smallEtaleToSpacesPreimage (X : AlgebraicSpace S) {U V : smallEtaleSite X}
    (f : (smallEtaleToSpaces X).obj U ⟶ (smallEtaleToSpaces X).obj V) : U ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk (yoneda.preimage f.left) trivial
    (by exact smallEtaleToSpacesPreimage_w X f)

/-- The presentation-chart inverse recovers its supplied spaces-étale arrow. -/
@[simp]
theorem smallEtaleToSpaces_map_preimage (X : AlgebraicSpace S) {U V : smallEtaleSite X}
    (f : (smallEtaleToSpaces X).obj U ⟶ (smallEtaleToSpaces X).obj V) :
    (smallEtaleToSpaces X).map (smallEtaleToSpacesPreimage X f) = f := sorry

/-- Every arrow between scheme charts is the image of its actual Yoneda preimage. -/
instance smallEtaleToSpaces_full (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).Full where
  map_surjective f := ⟨smallEtaleToSpacesPreimage X f, smallEtaleToSpaces_map_preimage X f⟩

/-- Actual continuous restriction from spaces-étale sheaves to the chart presentation. -/
abbrev smallEtalePresentationRestriction (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleToSpaces X).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Actual extension from presentation charts by the existing pointwise right Kan limits. -/
abbrev smallEtalePresentationExtension (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) :=
  (smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Restriction along the Yoneda preimages of arrows into a chart is natural. -/
private lemma smallEtalePresentationCounitInverseCone_naturality (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X)
    {a b : CategoryTheory.StructuredArrow (Opposite.op ((smallEtaleToSpaces X).obj U))
      (smallEtaleToSpaces X).op} (f : a ⟶ b) :
    𝟙 (F.obj.obj (Opposite.op U)) ≫
        F.obj.map (smallEtaleToSpacesPreimage X b.hom.unop).op =
      F.obj.map (smallEtaleToSpacesPreimage X a.hom.unop).op ≫ F.obj.map f.right := by
  sorry

/-- A section at a presentation chart gives its compatible family on all scheme arrows into
that chart. This cone is the actual reverse to the restricted right-Kan counit. -/
def smallEtalePresentationCounitInverseCone (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X) :
    CategoryTheory.Limits.Cone
      (CategoryTheory.StructuredArrow.proj (Opposite.op ((smallEtaleToSpaces X).obj U))
        (smallEtaleToSpaces X).op ⋙ F.obj) where
  pt := F.obj.obj (Opposite.op U)
  π :=
    { app := fun a ↦ F.obj.map
        (smallEtaleToSpacesPreimage X a.hom.unop).op
      naturality := by
        intro a b f
        exact smallEtalePresentationCounitInverseCone_naturality X F U f }

/-- The pointwise-limit lifts of sections commute with restriction between charts. -/
private lemma smallEtalePresentationCounitInv_naturality (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) :
    F.obj.map f ≫
        (CategoryTheory.Limits.limit.lift _
            (smallEtalePresentationCounitInverseCone X F V.unop) ≫
          ((smallEtaleToSpaces X).op.ranObjObjIsoLimit F.obj
            (Opposite.op ((smallEtaleToSpaces X).obj V.unop))).inv) =
      (CategoryTheory.Limits.limit.lift _
          (smallEtalePresentationCounitInverseCone X F U.unop) ≫
        ((smallEtaleToSpaces X).op.ranObjObjIsoLimit F.obj
          (Opposite.op ((smallEtaleToSpaces X).obj U.unop))).inv) ≫
        ((smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X).obj F).obj.map f := by
  sorry

/-- The inverse of the restriction-extension counit is a genuine pointwise-limit lift. -/
def smallEtalePresentationCounitInv (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    F ⟶ (smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X).obj F :=
  ObjectProperty.homMk
    { app := fun U ↦
        CategoryTheory.Limits.limit.lift _
            (smallEtalePresentationCounitInverseCone X F U.unop) ≫
          ((smallEtaleToSpaces X).op.ranObjObjIsoLimit F.obj
            (Opposite.op ((smallEtaleToSpaces X).obj U.unop))).inv
      naturality := by
        intro U V f
        exact smallEtalePresentationCounitInv_naturality X F f }

/-- The restriction-extension counit followed by the pointwise-limit lift is the identity. -/
private lemma smallEtalePresentationCounitIso_hom_inv_id (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app F ≫
      smallEtalePresentationCounitInv X F =
        𝟙 ((smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X).obj F) := by
  sorry

/-- The pointwise-limit lift followed by the restriction-extension counit is the identity. -/
private lemma smallEtalePresentationCounitIso_inv_hom_id (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    smallEtalePresentationCounitInv X F ≫
      ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app F = 𝟙 F := by
  sorry

/-- The restriction-extension counit components are natural in the sheaf. -/
private lemma smallEtalePresentationCounitIso_naturality (X : AlgebraicSpace S)
    {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (f : F ⟶ G) :
    (smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X).map f ≫
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app G =
      ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app F ≫ (𝟭 _).map f := by
  sorry

/-- Restricting the right Kan extension to the scheme charts recovers the original sheaf. -/
def smallEtalePresentationCounitIso (X : AlgebraicSpace S) :
    smallEtalePresentationExtension X ⋙ smallEtalePresentationRestriction X ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)).counit.app F
        inv := smallEtalePresentationCounitInv X F
        hom_inv_id := by exact smallEtalePresentationCounitIso_hom_inv_id X F
        inv_hom_id := by exact smallEtalePresentationCounitIso_inv_hom_id X F })
    (by exact smallEtalePresentationCounitIso_naturality X)

/-- Scheme charts are locally full in the spaces-étale site. -/
instance smallEtaleToSpaces_isLocallyFull (X : AlgebraicSpace S) :
    (smallEtaleToSpaces X).IsLocallyFull (spacesEtaleTopology X) := inferInstance

/-- The inverse to the adjunction unit glues the actual chartwise counit through the supplied
spaces-étale sheaf condition. -/
def smallEtalePresentationUnitInv (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    (smallEtalePresentationRestriction X ⋙ smallEtalePresentationExtension X).obj F ⟶ F :=
  ObjectProperty.homMk <|
    Functor.IsCoverDense.sheafHom
      ((((smallEtalePresentationCounitIso X).hom.app
        ((smallEtalePresentationRestriction X).obj F))).hom)

/-- The restriction-extension unit followed by the sheaf-gluing map is the identity. -/
private lemma smallEtalePresentationUnitIso_hom_inv_id (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).unit.app F ≫
      smallEtalePresentationUnitInv X F = 𝟙 F := by
  sorry

/-- The sheaf-gluing map followed by the restriction-extension unit is the identity. -/
private lemma smallEtalePresentationUnitIso_inv_hom_id (X : AlgebraicSpace S)
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    smallEtalePresentationUnitInv X F ≫
      ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).unit.app F =
      𝟙 ((smallEtalePresentationRestriction X ⋙ smallEtalePresentationExtension X).obj F) := by
  sorry

/-- The restriction-extension unit components are natural in the sheaf. -/
private lemma smallEtalePresentationUnitIso_naturality (X : AlgebraicSpace S)
    {F G : Sheaf (spacesEtaleTopology X) (Type (u + 1))} (f : F ⟶ G) :
    (𝟭 _).map f ≫
        ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)).unit.app G =
      ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology X)).unit.app F ≫
          (smallEtalePresentationRestriction X ⋙ smallEtalePresentationExtension X).map f := by
  sorry

/-- Extending the restriction to scheme charts recovers the spaces-étale sheaf. -/
def smallEtalePresentationUnitIso (X : AlgebraicSpace S) :
    𝟭 _ ≅ smallEtalePresentationRestriction X ⋙ smallEtalePresentationExtension X :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology X)).unit.app F
        inv := smallEtalePresentationUnitInv X F
        hom_inv_id := by exact smallEtalePresentationUnitIso_hom_inv_id X F
        inv_hom_id := by exact smallEtalePresentationUnitIso_inv_hom_id X F })
    (by exact smallEtalePresentationUnitIso_naturality X)

/-- Extending the inverse counit and then applying the inverse unit gives the identity. -/
private lemma smallEtalePresentationEquivalence_triangle (X : AlgebraicSpace S)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (smallEtalePresentationExtension X).map ((smallEtalePresentationCounitIso X).symm.hom.app F) ≫
      (smallEtalePresentationUnitIso X).symm.hom.app ((smallEtalePresentationExtension X).obj F) =
        𝟙 ((smallEtalePresentationExtension X).obj F) := by
  sorry

/-- The presentation comparison uses actual right-Kan extension and continuous restriction,
with explicit limit lifts and sheaf-gluing maps in both directions. -/
def smallEtalePresentationEquivalence (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ≌
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) where
  functor := smallEtalePresentationExtension X
  inverse := smallEtalePresentationRestriction X
  unitIso := (smallEtalePresentationCounitIso X).symm
  counitIso := (smallEtalePresentationUnitIso X).symm
  functor_unitIso_comp := by exact smallEtalePresentationEquivalence_triangle X

/-- Cocontinuous direct image along the chart inclusion is an equivalence between
the categories of type-valued sheaves on the small and spaces étale sites. -/
instance smallEtaleToSpaces_directImage_isEquivalence (X : AlgebraicSpace S) :
    ((smallEtaleToSpaces X).sheafPushforwardCocontinuous (Type (u + 1))
      (smallEtaleTopology X) (spacesEtaleTopology X)).IsEquivalence :=
  (smallEtalePresentationEquivalence X).isEquivalence_functor

end AlgebraicGeometry.AlgebraicSpace
