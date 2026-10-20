module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Glueing sheaves on small étale sites of algebraic spaces

A sheaf of sets on `X_étale` determines a sheaf on `U_étale` for every object
`U` of `X_étale`, together with inverse-image transition isomorphisms along
morphisms of `X_étale`. This module packages those compatible systems.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing

variable {S : Scheme.{u}}

/-- Pullback of Type-valued sheaves along a morphism of `X_étale`, as inverse image of
`f_small`. -/
noncomputable def pullback {X : AlgebraicSpace S} {U V : smallEtaleSite X} (f : V ⟶ U) :
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology (ofOver V.left)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi (ofOverMap f.left)).inverseImage

/-- Pullback along an identity is canonically isomorphic to the identity on small étale
sheaves. -/
noncomputable def pullbackId {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    pullback (𝟙 U) ≅ 𝟭 (Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1))) :=
  eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      (ofOverMap_id U.left)) ≪≫
    smallEtaleMorphismOfTopoi_etaleRestrictionSheaf (𝟙 (ofOver U.left)) ≪≫
    Functor.sheafPushforwardContinuousId'
      (eqToIso (etaleRestriction_id (ofOver U.left)))
      (Type (u + 1)) (smallEtaleTopology (ofOver U.left))

/-- Successive pullbacks of small étale sheaves are canonically isomorphic to pullback along
the composite. -/
noncomputable def pullbackComp {X : AlgebraicSpace S} {U V W : smallEtaleSite X}
    (f : V ⟶ U) (g : W ⟶ V) :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  (smallEtaleMorphismOfTopoiComp (ofOverMap g.left) (ofOverMap f.left)).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage)
      (ofOverMap_comp f.left g.left).symm)

/-- A compatible system of sheaves on the small étale sites of schemes étale over an
algebraic space. -/
structure Object {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The sheaf on the small étale site of a scheme étale over `X`. -/
  obj (U : smallEtaleSite X) : Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1))
  /-- The inverse-image transition isomorphism `c_f : f_small⁻¹ F_U ≅ F_{U'}`. -/
  transition {U V : smallEtaleSite X} (f : V ⟶ U) : (pullback f).obj (obj U) ≅ obj V
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (U : smallEtaleSite X) :
    transition (𝟙 U) = (pullbackId U).app (obj U)
  /-- The transitions satisfy the inverse-image cocycle
  `c_g ∘ g_small⁻¹ c_f = c_{f ∘ g}`. -/
  transition_comp {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V) :
    (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
      (pullback g).mapIso (transition f) ≪≫ transition g

namespace Object

variable {X : AlgebraicSpace S}

/-- The fields of a compatible small-étale system express identity and the cocycle
condition for its transition isomorphisms. -/
theorem spec (F : Object X) :
    (∀ U : smallEtaleSite X, F.transition (𝟙 U) = (pullbackId U).app (F.obj U)) ∧
      (∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
        (pullbackComp f g).app (F.obj U) ≪≫ F.transition (g ≫ f) =
          (pullback g).mapIso (F.transition f) ≪≫ F.transition g) :=
  ⟨F.transition_id, F.transition_comp⟩

/-- The identity transition follows from the composition cocycle and invertibility. -/
theorem transition_id_of_comp (obj : ∀ U : smallEtaleSite X,
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)))
    (transition : ∀ {U V : smallEtaleSite X} (f : V ⟶ U),
      (pullback f).obj (obj U) ≅ obj V)
    (transition_comp : ∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
      (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
        (pullback g).mapIso (transition f) ≪≫ transition g) :
    ∀ U : smallEtaleSite X, transition (𝟙 U) = (pullbackId U).app (obj U) := by
  sorry

/-- Construct a compatible system from local sheaves and transition isomorphisms
satisfying the composition cocycle. -/
noncomputable def ofTransitions (obj : ∀ U : smallEtaleSite X,
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)))
    (transition : ∀ {U V : smallEtaleSite X} (f : V ⟶ U),
      (pullback f).obj (obj U) ≅ obj V)
    (transition_comp : ∀ {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V),
      (pullbackComp f g).app (obj U) ≪≫ transition (g ≫ f) =
        (pullback g).mapIso (transition f) ≪≫ transition g) : Object X where
  obj := obj
  transition := transition
  transition_id := transition_id_of_comp obj transition transition_comp
  transition_comp := transition_comp

end Object

/-- A morphism of compatible small-étale systems is a componentwise sheaf morphism
commuting with every transition isomorphism. -/
@[ext]
structure Hom {X : AlgebraicSpace S} (F G : Object X) where
  /-- The component over an object of `X_étale`. -/
  app (U : smallEtaleSite X) : F.obj U ⟶ G.obj U
  /-- Component maps commute with inverse-image transitions. -/
  naturality {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (app U)) (F.transition f).hom (G.transition f).hom (app V)

namespace Hom

variable {X : AlgebraicSpace S}

/-- The component identities form a morphism of compatible systems. -/
theorem id_naturality (F : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (𝟙 (F.obj U))) (F.transition f).hom
      (F.transition f).hom (𝟙 (F.obj V)) := by
  sorry

/-- Composites of component morphisms commute with transitions. -/
theorem comp_naturality {F G H : Object X} (α : Hom F G) (β : Hom G H)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map (α.app U ≫ β.app U)) (F.transition f).hom
      (H.transition f).hom (α.app V ≫ β.app V) := by
  sorry

/-- The identity compatible morphism. -/
def id (F : Object X) : Hom F F where
  app U := 𝟙 (F.obj U)
  naturality f := id_naturality F f

/-- Composition of compatible morphisms. -/
def comp {F G H : Object X} (α : Hom F G) (β : Hom G H) : Hom F H where
  app U := α.app U ≫ β.app U
  naturality f := comp_naturality α β f

/-- The identity acts on either side of a compatible morphism. -/
theorem id_comp {F G : Object X} (α : Hom F G) : comp (id F) α = α := by
  sorry

/-- Composing with the identity on the target preserves a compatible morphism. -/
theorem comp_id {F G : Object X} (α : Hom F G) : comp α (id G) = α := by
  sorry

/-- Composition of compatible morphisms is associative. -/
theorem assoc {F G H K : Object X} (α : Hom F G) (β : Hom G H) (γ : Hom H K) :
    comp (comp α β) γ = comp α (comp β γ) := by
  sorry

end Hom

/-- The category of compatible systems, bundled without installing a global category
instance on the explicit object structure. -/
noncomputable def category (X : AlgebraicSpace S) : Cat :=
  { α := Object X
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := Hom.id_comp
        comp_id := Hom.comp_id
        assoc := Hom.assoc } }

/-- The sheaf on `U_étale` obtained by inverse image along the structure morphism of
`U`. -/
noncomputable def fromSheafObj {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X) :
    Sheaf (smallEtaleTopology (ofOver U.left)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi U.hom).inverseImage.obj F

/-- The canonical transition of the compatible system associated to a sheaf on
`X_étale`. -/
noncomputable def fromSheafTransition {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (pullback f).obj (fromSheafObj F U) ≅ fromSheafObj F V :=
  ((smallEtaleMorphismOfTopoiComp (ofOverMap f.left) U.hom).app F).symm ≪≫
    eqToIso (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj F)
      (ofOverMap_triangle f))

/-- The transitions obtained from inverse image satisfy the composition cocycle. -/
theorem Object.ofSheaf_transition_comp {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U V W : smallEtaleSite X} (f : V ⟶ U) (g : W ⟶ V) :
    (pullbackComp f g).app (fromSheafObj F U) ≪≫ fromSheafTransition F (g ≫ f) =
      (pullback g).mapIso (fromSheafTransition F f) ≪≫ fromSheafTransition F g := by
  sorry

namespace Object

variable {X : AlgebraicSpace S}

/-- The compatible system of small étale sheaves obtained by inverse image from a sheaf
on `X_étale`. -/
noncomputable def ofSheaf (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) : Object X :=
  ofTransitions (fromSheafObj F) (fromSheafTransition F) (ofSheaf_transition_comp F)

end Object

/-- Inverse image carries a sheaf morphism to a morphism of compatible systems. -/
theorem fromSheafMap_naturality {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (η : F ⟶ G)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq ((pullback f).map ((smallEtaleMorphismOfTopoi U.hom).inverseImage.map η))
      (fromSheafTransition F f).hom (fromSheafTransition G f).hom
      ((smallEtaleMorphismOfTopoi V.hom).inverseImage.map η) := by
  sorry

/-- A morphism of sheaves on `X_étale` induces the componentwise compatible morphism
between their inverse-image systems. -/
noncomputable def fromSheafMap {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) (Type (u + 1))} (η : F ⟶ G) :
    Hom (Object.ofSheaf F) (Object.ofSheaf G) where
  app U := (smallEtaleMorphismOfTopoi U.hom).inverseImage.map η
  naturality f := fromSheafMap_naturality η f

/-- Inverse image preserves identity morphisms of sheaves. -/
theorem fromSheaf_map_id {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    fromSheafMap (𝟙 F) = Hom.id (Object.ofSheaf F) := by
  sorry

/-- Inverse image preserves composition of sheaf morphisms. -/
theorem fromSheaf_map_comp {X : AlgebraicSpace S}
    {F G H : Sheaf (smallEtaleTopology X) (Type (u + 1))} (η : F ⟶ G) (θ : G ⟶ H) :
    fromSheafMap (η ≫ θ) = Hom.comp (fromSheafMap η) (fromSheafMap θ) := by
  sorry

/-- Inverse image of sheaves on `X_étale` to compatible systems on all `U_étale`. -/
noncomputable def fromSheaf (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ category X where
  obj := Object.ofSheaf
  map := fromSheafMap
  map_id := fromSheaf_map_id
  map_comp := fromSheaf_map_comp

variable {X : AlgebraicSpace S}

/-- The object of the compatible system associated to a sheaf is inverse image along the
structure morphism. -/
theorem fromSheaf_obj (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (U : smallEtaleSite X) :
    ((fromSheaf X).obj F).obj U = (smallEtaleMorphismOfTopoi U.hom).inverseImage.obj F :=
  rfl

/-- The transition of the compatible system associated to a sheaf is the functoriality
isomorphism of inverse image. -/
theorem fromSheaf_transition (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    ((fromSheaf X).obj F).transition f = fromSheafTransition F f :=
  rfl

/-- Restriction of reconstructed global sections along a morphism of `X_étale`. -/
noncomputable def toSheafMap (G : Object X) {U V : smallEtaleSite X} (f : V ⟶ U) :
    (G.obj U).obj.obj (op (idObj U.left)) ⟶ (G.obj V).obj.obj (op (idObj V.left)) :=
  (G.obj U).obj.map (idObjHom f).op ≫
    (smallEtaleMorphismOfTopoi_inverseImage_obj (ofOverMap f.left) (G.obj U)
        (idObj V.left)).inv ≫
      (G.transition f).hom.hom.app (op (idObj V.left))

/-- Restriction of reconstructed sections preserves identity maps. -/
theorem toSheafPresheaf_map_id (G : Object X) (U : smallEtaleSite X) :
    toSheafMap G (𝟙 U) = 𝟙 _ := by
  sorry

/-- Restriction of reconstructed sections preserves composition. -/
theorem toSheafPresheaf_map_comp (G : Object X) {U V W : smallEtaleSite X}
    (f : V ⟶ U) (g : W ⟶ V) :
    toSheafMap G f ≫ toSheafMap G g = toSheafMap G (g ≫ f) := by
  sorry

/-- The presheaf on `X_étale` reconstructed from terminal sections of a compatible
system. -/
noncomputable def toSheafPresheaf (G : Object X) : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1) where
  obj U := (G.obj U.unop).obj.obj (op (idObj U.unop.left))
  map f := toSheafMap G f.unop
  map_id := by
    intro U
    exact toSheafPresheaf_map_id G U.unop
  map_comp := by
    intro U V W f g
    exact (toSheafPresheaf_map_comp G f.unop g.unop).symm

/-- The reconstructed presheaf of a compatible system is a sheaf on `X_étale`. -/
theorem toSheaf_isSheaf (G : Object X) :
    Presheaf.IsSheaf (smallEtaleTopology X) (toSheafPresheaf G) := by
  sorry

/-- Component maps on compatible systems induce natural transformations on
reconstructed presheaves. -/
theorem toSheaf_map_naturality {G H : Object X} (α : Hom G H)
    {U V : smallEtaleSite X} (f : V ⟶ U) :
    CommSq (toSheafMap G f)
      ((α.app U).hom.app (op (idObj U.left)))
      ((α.app V).hom.app (op (idObj V.left)))
      (toSheafMap H f) := by
  sorry

/-- Reconstructed component maps preserve identity morphisms. -/
theorem toSheaf_map_id (G : Object X) (U : smallEtaleSite X) :
    ((Hom.id G).app U).hom.app (op (idObj U.left)) =
      𝟙 ((G.obj U).obj.obj (op (idObj U.left))) := by
  sorry

/-- Reconstructed component maps preserve composition. -/
theorem toSheaf_map_comp {G H K : Object X} (α : Hom G H) (β : Hom H K)
    (U : smallEtaleSite X) :
    ((Hom.comp α β).app U).hom.app (op (idObj U.left)) =
      ((α.app U).hom ≫ (β.app U).hom).app (op (idObj U.left)) := by
  sorry

/-- Reconstruction of a sheaf on `X_étale` from a compatible system of sheaves on all
`U_étale`. -/
noncomputable def toSheaf (X : AlgebraicSpace S) :
    category X ⥤ Sheaf (smallEtaleTopology X) (Type (u + 1)) := by
  let obj' (G : Object X) : Sheaf (smallEtaleTopology X) (Type (u + 1)) :=
    ⟨toSheafPresheaf G, toSheaf_isSheaf G⟩
  let map' {G H : Object X} (α : Hom G H) : obj' G ⟶ obj' H :=
    ObjectProperty.homMk
      { app := fun U ↦ (α.app U.unop).hom.app (op (idObj U.unop.left))
        naturality := by
          intro U V f
          exact (toSheaf_map_naturality α f.unop).w }
  refine
    { obj := obj'
      map := map'
      map_id := ?_
      map_comp := ?_ }
  · intro G
    apply ObjectProperty.hom_ext
    ext U x
    exact congrArg (fun f => f x) (toSheaf_map_id G U.unop)
  · intro G H K α β
    apply ObjectProperty.hom_ext
    ext U x
    exact congrArg (fun f => f x) (toSheaf_map_comp α β U.unop)

/-- Reconstructed sections of a compatible system at `U` are the sections of `F_U` at the
identity object of `U_étale`. -/
theorem toSheaf_obj (G : Object X) (U : smallEtaleSite X) :
    ((toSheaf X).obj G).obj.obj (op U) = (G.obj U).obj.obj (op (idObj U.left)) :=
  rfl

/-- Inverse image from sheaves on `X_étale` to compatible systems on all small étale sites
is an equivalence of categories. -/
instance fromSheaf_isEquivalence (X : AlgebraicSpace S) :
    (fromSheaf X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SmallEtaleGlueing
