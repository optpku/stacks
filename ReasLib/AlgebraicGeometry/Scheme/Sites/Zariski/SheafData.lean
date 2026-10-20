module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
public import ReasLib.Topology.Sheaves.Pullback.Composition

/-!
# Sheaves on the big Zariski site as compatible local sheaves

A sheaf of types on the big Zariski site over a scheme can be described by a
sheaf on every scheme over the base, together with compatible inverse-image
maps which are isomorphisms along open immersions.
-/

@[expose] public section

open CategoryTheory
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.Big

/-- A compatible family of sheaves on schemes over `S`, with transition maps in
the inverse-image direction. -/
structure SheafData (S : Scheme.{u}) where
  /-- The sheaf attached to a scheme over `S`. -/
  obj : ∀ T : Over S, TopCat.Sheaf (Type u) T.left.toTopCat
  /-- The inverse-image map attached to a morphism of schemes over `S`. -/
  pullbackMap : ∀ {T' T : Over S} (f : T' ⟶ T),
    (TopCat.Sheaf.pullback (Type u) f.left.base).obj (obj T) ⟶ obj T'
  /-- Transition maps agree with composition through the canonical comparison
  between iterated and composite inverse image. -/
  comp : ∀ {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T),
    (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app (obj T) ≫
        pullbackMap (g ≫ f) =
      (TopCat.Sheaf.pullback (Type u) g.left.base).map (pullbackMap f) ≫
        pullbackMap g
  /-- A transition map along an open immersion is an isomorphism. -/
  isIso_of_isOpenImmersion : ∀ {T' T : Over S} (f : T' ⟶ T)
    [IsOpenImmersion f.left], IsIso (pullbackMap f)

namespace SheafData

variable {S : Scheme.{u}}

/-- The composition and open-immersion conditions satisfied by a compatible
family of local sheaves. -/
theorem conditions (D : SheafData S) :
    (∀ {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T),
      (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app (D.obj T) ≫
          D.pullbackMap (g ≫ f) =
        (TopCat.Sheaf.pullback (Type u) g.left.base).map (D.pullbackMap f) ≫
          D.pullbackMap g) ∧
    (∀ {T' T : Over S} (f : T' ⟶ T) [IsOpenImmersion f.left],
      IsIso (D.pullbackMap f)) := sorry

/-- The sheaf on `T` obtained by restricting a big-Zariski sheaf to the small
Zariski site of `T` and transporting across the open-subscheme equivalence. -/
def ofSheafObj (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    (T : Over S) : TopCat.Sheaf (Type u) T.left.toTopCat :=
  (T.left.smallZariskiTypeSheafEquiv).functor.obj
    ((Zariski.SmallToBig.inverseImage T.hom).obj F)

/-- The object of the big Zariski slice represented by an open subset of a
scheme over `S`. -/
abbrev openOver (T : Over S) (U : T.left.Opens) : Over S :=
  { left := U
    right := ⟨⟨⟩⟩
    hom := U.ι ≫ T.hom }

/-- The source scheme of the object represented by an open subset is that open
subscheme. -/
theorem openOver_left (T : Over S) (U : T.left.Opens) :
    (openOver T U).left = U := rfl

/-- The structure morphism of the object represented by an open subset is the
open immersion followed by the ambient structure morphism. -/
theorem openOver_hom (T : Over S) (U : T.left.Opens) :
    (openOver T U).hom = U.ι ≫ T.hom := rfl

/-- The canonical morphism from an open subset, viewed over `S`, to its ambient
scheme over `S`. -/
def openOverHom (T : Over S) (U : T.left.Opens) : openOver T U ⟶ T :=
  Over.homMk U.ι

/-- The canonical morphism from an open subset to its ambient scheme is an
open immersion. -/
theorem openOverHom_isOpenImmersion (T : Over S) (U : T.left.Opens) :
    IsOpenImmersion (openOverHom T U).left := by
  change IsOpenImmersion U.ι
  infer_instance

/-- The morphism over `S` from the inverse image of an open subset to the open
subset itself. -/
def preimageOpenHom {T' T : Over S} (f : T' ⟶ T) (U : T.left.Opens) :
    openOver T' ((TopologicalSpace.Opens.map f.left.base).obj U) ⟶ openOver T U :=
  by
    refine Over.homMk
      (eqToHom (by rfl : (openOver T' (f.left ⁻¹ᵁ U)).left = (f.left ⁻¹ᵁ U)) ≫
        (f.left ∣_ U) ≫ eqToHom (by rfl : U = (openOver T U).left)) ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, openOver_hom]
    simp [Over.w f]

/-- Evaluation of the restricted local sheaf on an open subset is evaluation of
the original big-site sheaf on the corresponding object over `S`. -/
theorem ofSheafObj_obj_eq
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    (T : Over S) (U : T.left.Opens) :
    (ofSheafObj F T).presheaf.obj (op U) = F.obj.obj (op (openOver T U)) := rfl

/-- The restriction map of a big-site sheaf from an open subset to its inverse
image under a morphism over the base. -/
def ofSheafPullbackMapApp
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) (U : T.left.Opens) :
    (ofSheafObj F T).presheaf.obj (op U) ⟶
      (ofSheafObj F T').presheaf.obj
        (op ((TopologicalSpace.Opens.map f.left.base).obj U)) :=
  eqToHom (ofSheafObj_obj_eq F T U) ≫ F.obj.map (preimageOpenHom f U).op ≫
    eqToHom (ofSheafObj_obj_eq F T' ((TopologicalSpace.Opens.map f.left.base).obj U)).symm

/-- The objectwise restriction maps defining the transition associated to `f`
commute with restriction to smaller open subsets. -/
theorem ofSheafPullbackMapApp_naturality
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) {U V : T.left.Opens} (i : U ⟶ V) :
    (ofSheafObj F T).presheaf.map i.op ≫ ofSheafPullbackMapApp F f U =
      ofSheafPullbackMapApp F f V ≫
        (ofSheafObj F T').presheaf.map
          ((TopologicalSpace.Opens.map f.left.base).map i).op := sorry

/-- The adjoint form of the transition associated to a morphism over `S`. -/
def ofSheafAdjointMap
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) :
    ofSheafObj F T ⟶
      (TopCat.Sheaf.pushforward (Type u) f.left.base).obj (ofSheafObj F T') :=
  ObjectProperty.homMk
    { app := fun U ↦ ofSheafPullbackMapApp F f U.unop
      naturality := fun _ _ i ↦ ofSheafPullbackMapApp_naturality F f i.unop }

/-- The inverse-image transition associated to a morphism over `S`. -/
def ofSheafPullbackMap
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) :
    (TopCat.Sheaf.pullback (Type u) f.left.base).obj (ofSheafObj F T) ⟶
      ofSheafObj F T' :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.left.base).homEquiv
    (ofSheafObj F T) (ofSheafObj F T')).symm (ofSheafAdjointMap F f)

/-- The transitions obtained from a big-site sheaf respect composition. -/
theorem ofSheafPullbackMap_comp
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T) :
    (TopCat.Sheaf.pullbackComp g.left.base f.left.base).hom.app (ofSheafObj F T) ≫
        ofSheafPullbackMap F (g ≫ f) =
      (TopCat.Sheaf.pullback (Type u) g.left.base).map (ofSheafPullbackMap F f) ≫
        ofSheafPullbackMap F g := sorry

/-- A transition obtained from a big-site sheaf is an isomorphism along an open
immersion. -/
theorem ofSheafPullbackMap_isIso_of_isOpenImmersion
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) [IsOpenImmersion f.left] :
    IsIso (ofSheafPullbackMap F f) := sorry

/-- Restrict a sheaf on the big Zariski site to its compatible family of local
sheaves. -/
def ofSheaf (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u)) : SheafData S where
  obj := ofSheafObj F
  pullbackMap := ofSheafPullbackMap F
  comp := ofSheafPullbackMap_comp F
  isIso_of_isOpenImmersion := ofSheafPullbackMap_isIso_of_isOpenImmersion F

/-- The map on global sections induced by a transition in a compatible family. -/
def toPresheafMap (D : SheafData S) {T' T : Over S} (f : T' ⟶ T) :
    (D.obj T).presheaf.obj (op (⊤ : T.left.Opens)) ⟶
      (D.obj T').presheaf.obj (op (⊤ : T'.left.Opens)) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f.left.base).homEquiv
    (D.obj T) (D.obj T')) (D.pullbackMap f)).hom.app (op (⊤ : T.left.Opens))

/-- The map on global sections associated to an identity morphism is the
identity. -/
theorem toPresheafMap_id (D : SheafData S) (T : Over S) :
    toPresheafMap D (𝟙 T) = 𝟙 _ := sorry

/-- Maps on global sections compose contravariantly with morphisms over the
base. -/
theorem toPresheafMap_comp (D : SheafData S)
    {T'' T' T : Over S} (g : T'' ⟶ T') (f : T' ⟶ T) :
    toPresheafMap D (g ≫ f) = toPresheafMap D f ≫ toPresheafMap D g := sorry

/-- The presheaf on the big Zariski site obtained from the global sections of
a compatible family of local sheaves. -/
def toPresheaf (D : SheafData S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (D.obj T.unop).presheaf.obj (op (⊤ : T.unop.left.Opens))
  map f := toPresheafMap D f.unop
  map_id T := toPresheafMap_id D T.unop
  map_comp f g := toPresheafMap_comp D g.unop f.unop

/-- The presheaf reconstructed from a compatible family satisfies the big
Zariski sheaf condition. -/
theorem toPresheaf_isSheaf (D : SheafData S) :
    CategoryTheory.Presheaf.IsSheaf S.bigZariskiTopology (toPresheaf D) := sorry

/-- Reconstruct the big-Zariski sheaf whose value on `T/S` is the global
sections of the local sheaf attached to `T`. -/
def toSheaf (D : SheafData S) :
    CategoryTheory.Sheaf S.bigZariskiTopology (Type u) :=
  ⟨toPresheaf D, toPresheaf_isSheaf D⟩

/-- The object represented by the full open subset of `T` is canonically
isomorphic to `T` over the base. -/
def openOverTopIso (T : Over S) : openOver T (⊤ : T.left.Opens) ≅ T :=
  Over.isoMk T.left.topIso (by rfl)

/-- The component at `T/S` of the comparison from reconstructing a restricted
big-site sheaf back to the original sheaf. -/
def toSheafOfSheafIsoApp
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u)) (T : Over S) :
    (toSheaf (ofSheaf F)).obj.obj (op T) ≅ F.obj.obj (op T) :=
  eqToIso (ofSheafObj_obj_eq F T (⊤ : T.left.Opens)) ≪≫
    (F.obj.mapIso (openOverTopIso T).op).symm

/-- The reconstruction comparison for a big-site sheaf is natural in schemes
over the base. -/
theorem toSheafOfSheafIsoApp_naturality
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u))
    {T' T : Over S} (f : T' ⟶ T) :
    (toSheaf (ofSheaf F)).obj.map f.op ≫ (toSheafOfSheafIsoApp F T').hom =
      (toSheafOfSheafIsoApp F T).hom ≫ F.obj.map f.op := sorry

/-- Reconstructing a big-Zariski sheaf from its compatible local family gives
back the original sheaf. -/
def toSheaf_ofSheafIso
    (F : CategoryTheory.Sheaf S.bigZariskiTopology (Type u)) :
    toSheaf (ofSheaf F) ≅ F :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun T ↦ toSheafOfSheafIsoApp F T.unop)
    (fun f ↦ toSheafOfSheafIsoApp_naturality F f.unop)

/-- The transition along the inclusion of an open subset, followed by the
canonical open-embedding comparison, identifies the local sheaf on the open
with the naive restriction of the ambient local sheaf. -/
def openTransitionIso (D : SheafData S) (T : Over S) (U : T.left.Opens) :
    D.obj (openOver T U) ≅
      (U.ι.isOpenEmbedding.sheafPullback (Type u)).obj (D.obj T) :=
  (@asIso _ _ _ _ (D.pullbackMap (openOverHom T U))
    (@SheafData.isIso_of_isOpenImmersion S D _ _ (openOverHom T U)
      (openOverHom_isOpenImmersion T U))).symm ≪≫
      (U.ι.isOpenEmbedding.sheafPullbackIso (Type u)).app (D.obj T)

/-- On the full open subset, the open-transition isomorphism identifies global
sections on the open with sections of the ambient sheaf on that open. -/
def openTransitionIsoTopApp (D : SheafData S) (T : Over S) (U : T.left.Opens) :
    (D.obj (openOver T U)).presheaf.obj (op (⊤ : U.toScheme.Opens)) ≅
      (D.obj T).presheaf.obj (op U) :=
  ((TopCat.Sheaf.forget (Type u) U.toScheme.toTopCat).mapIso
    (openTransitionIso D T U)).app (op (⊤ : U.toScheme.Opens)) ≪≫
      eqToIso (congrArg
        (fun V : T.left.Opens ↦ (D.obj T).presheaf.obj (op V))
        U.ι_image_top)

/-- The objectwise comparison between a local sheaf and the local sheaf
recovered from its global-section reconstruction. -/
def ofSheafToSheafIsoComponent (D : SheafData S) (T : Over S)
    (U : T.left.Opens) :
    ((ofSheaf (toSheaf D)).obj T).presheaf.obj (op U) ≅
      (D.obj T).presheaf.obj (op U) :=
  eqToIso (ofSheafObj_obj_eq (toSheaf D) T U) ≪≫ openTransitionIsoTopApp D T U

/-- Naturality of the reconstruction components on the open subsets of every
scheme over `S`. -/
def LocalReconstructionNaturality (D : SheafData S) : Prop :=
  ∀ (T : Over S) {U V : T.left.Opens} (i : U ⟶ V),
    ((ofSheaf (toSheaf D)).obj T).presheaf.map i.op ≫
        (ofSheafToSheafIsoComponent D T U).hom =
      (ofSheafToSheafIsoComponent D T V).hom ≫
        (D.obj T).presheaf.map i.op

/-- The local-sheaf isomorphism obtained from the objectwise reconstruction
components and a proof of their naturality. -/
def ofSheafToSheafIsoAppOf (D : SheafData S)
    (h : LocalReconstructionNaturality D) (T : Over S) :
    (ofSheaf (toSheaf D)).obj T ≅ D.obj T :=
  ObjectProperty.isoMk _ <| NatIso.ofComponents
    (fun U ↦ ofSheafToSheafIsoComponent D T U.unop)
    (fun i ↦ h T i.unop)

/-- The local reconstruction components are natural in open subsets and their
resulting local-sheaf isomorphisms commute with every transition map. -/
theorem ofSheafToSheafIsoApp_naturality (D : SheafData S) :
    ∃ h : LocalReconstructionNaturality D,
      ∀ {T' T : Over S} (f : T' ⟶ T),
        (ofSheaf (toSheaf D)).pullbackMap f ≫
            (ofSheafToSheafIsoAppOf D h T').hom =
          (TopCat.Sheaf.pullback (Type u) f.left.base).map
              (ofSheafToSheafIsoAppOf D h T).hom ≫ D.pullbackMap f := sorry

/-- The canonical proof that the local reconstruction components form
natural transformations on open subsets. -/
theorem localReconstructionNaturality (D : SheafData S) :
    LocalReconstructionNaturality D :=
  (ofSheafToSheafIsoApp_naturality D).choose

/-- The local-sheaf isomorphism obtained from the objectwise reconstruction
components. -/
def ofSheafToSheafIsoApp (D : SheafData S) (T : Over S) :
    (ofSheaf (toSheaf D)).obj T ≅ D.obj T :=
  ofSheafToSheafIsoAppOf D (localReconstructionNaturality D) T

/-- A pointwise isomorphism of compatible local sheaf families which commutes
with all transition maps. -/
structure Iso (D E : SheafData S) where
  /-- The isomorphism of local sheaves at each scheme over the base. -/
  app : ∀ T : Over S, D.obj T ≅ E.obj T
  /-- Compatibility of the pointwise isomorphisms with inverse-image
  transition maps. -/
  naturality : ∀ {T' T : Over S} (f : T' ⟶ T),
    D.pullbackMap f ≫ (app T').hom =
      (TopCat.Sheaf.pullback (Type u) f.left.base).map (app T).hom ≫
        E.pullbackMap f

/-- A compatible local family is recovered, up to a transition-compatible
pointwise isomorphism, from its reconstructed big-site sheaf. -/
def ofSheaf_toSheafIso (D : SheafData S) : Iso (ofSheaf (toSheaf D)) D where
  app := ofSheafToSheafIsoApp D
  naturality f := (ofSheafToSheafIsoApp_naturality D).choose_spec f

end SheafData

/-- Explicit mutually inverse constructions between big-Zariski sheaves and
compatible families of sheaves on schemes over the base. -/
structure SheafDataEquivalence (S : Scheme.{u}) where
  /-- Restrict a big-site sheaf to a compatible local family. -/
  ofSheaf : CategoryTheory.Sheaf S.bigZariskiTopology (Type u) → SheafData S
  /-- Reconstruct a big-site sheaf from a compatible local family. -/
  toSheaf : SheafData S → CategoryTheory.Sheaf S.bigZariskiTopology (Type u)
  /-- Reconstruction after restriction recovers the original big-site sheaf. -/
  toSheaf_ofSheafIso : ∀ F, toSheaf (ofSheaf F) ≅ F
  /-- Restriction after reconstruction recovers the original local family by
  transition-compatible pointwise isomorphisms. -/
  ofSheaf_toSheafIso : ∀ D, SheafData.Iso (ofSheaf (toSheaf D)) D

/-- The canonical characterization of big-Zariski sheaves by compatible
families of sheaves on schemes over the base. -/
def sheafDataEquivalence (S : Scheme.{u}) : SheafDataEquivalence S where
  ofSheaf := SheafData.ofSheaf
  toSheaf := SheafData.toSheaf
  toSheaf_ofSheafIso := SheafData.toSheaf_ofSheafIso
  ofSheaf_toSheafIso := SheafData.ofSheaf_toSheafIso

end AlgebraicGeometry.Scheme.Zariski.Big
