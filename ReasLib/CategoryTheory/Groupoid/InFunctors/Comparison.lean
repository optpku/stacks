module

public import ReasLib.CategoryTheory.Groupoid.InFunctors
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatIso

/-!
# Comparison with groupoid-valued functors

Groupoid-valued functors have explicit presentations by object and arrow functors.
Morphisms of presentations correspond to natural transformations of their evaluations.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

namespace Hom

/-- Fibrewise functors induced by a presentation morphism commute with base transitions. -/
theorem toNatTrans_naturality {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H)
    {T T' : C} (transition : T ⟶ T') :
    G.toFunctor.map transition ≫ f.mapPoints T' =
      f.mapPoints T ≫ H.toFunctor.map transition := sorry

/-- The natural transformation induced by a morphism of groupoids in functors. -/
def toNatTrans {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    G.toFunctor ⟶ H.toFunctor where
  app T := f.mapPoints T
  naturality := fun _ _ transition ↦ toNatTrans_naturality f transition

/-- The components of the induced natural transformation are the fibrewise functors. -/
theorem toNatTrans_app {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) (T : C) :
    (toNatTrans f).app T = f.mapPoints T := rfl

/-- The object maps of a natural transformation commute with base transitions. -/
theorem ofNatTrans_obj_naturality {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) {T T' : C} (transition : T ⟶ T') :
    G.U.map transition ≫ TypeCat.ofHom (fun x ↦ (α.app T').obj x) =
      TypeCat.ofHom (fun x ↦ (α.app T).obj x) ≫ H.U.map transition := sorry

/-- The arrow maps of a natural transformation commute with base transitions. -/
theorem ofNatTrans_arrow_naturality {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) {T T' : C} (transition : T ⟶ T') :
    G.R.map transition ≫ TypeCat.ofHom
        (fun a ↦ ((α.app T').map (PointHom.ofArrow a rfl rfl)).arrow) =
      TypeCat.ofHom (fun a ↦ ((α.app T).map (PointHom.ofArrow a rfl rfl)).arrow) ≫
        H.R.map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def objectTransformation {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) : G.U ⟶ H.U where
  app T := TypeCat.ofHom fun x ↦ (α.app T).obj x
  naturality := fun _ _ transition ↦ ofNatTrans_obj_naturality α transition

set_option backward.privateInPublic true in
@[expose] private def arrowTransformation {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) : G.R ⟶ H.R where
  app T := TypeCat.ofHom fun a ↦ ((α.app T).map (PointHom.ofArrow a rfl rfl)).arrow
  naturality := fun _ _ transition ↦ ofNatTrans_arrow_naturality α transition

/-- The object and arrow maps induced by a natural transformation preserve sources. -/
private theorem ofNatTrans_map_s {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) :
    G.s ≫ objectTransformation α = arrowTransformation α ≫ H.s := sorry

/-- The object and arrow maps induced by a natural transformation preserve targets. -/
private theorem ofNatTrans_map_t {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) :
    G.t ≫ objectTransformation α = arrowTransformation α ≫ H.t := sorry

/-- The arrow map induced by a natural transformation preserves composition. -/
private theorem ofNatTrans_map_c {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) :
    G.c ≫ arrowTransformation α =
      GroupoidInFunctors.composableMap (objectTransformation α) (arrowTransformation α)
        (ofNatTrans_map_s α) (ofNatTrans_map_t α) ≫ H.c := sorry

set_option backward.privateInPublic true in
/-- The presentation morphism induced by a natural transformation of evaluated groupoids. -/
def ofNatTrans {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) : Hom G H where
  obj := objectTransformation α
  arrow := arrowTransformation α
  map_s := private ofNatTrans_map_s α
  map_t := private ofNatTrans_map_t α
  map_c := private ofNatTrans_map_c α

/-- The reconstructed object map is the object map of the corresponding component. -/
theorem ofNatTrans_obj {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) (T : C) (x : G.U.obj T) :
    (ofNatTrans α).obj.app T x = (α.app T).obj x := rfl

/-- The reconstructed arrow map is the arrow map of the corresponding component. -/
theorem ofNatTrans_arrow {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) (T : C) (a : G.R.obj T) :
    (ofNatTrans α).arrow.app T a =
      ((α.app T).map (PointHom.ofArrow a rfl rfl)).arrow := rfl

/-- Reconstructing the natural transformation of a presentation morphism recovers it. -/
theorem ofNatTrans_toNatTrans {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    ofNatTrans (toNatTrans f) = f := sorry

/-- Evaluating the reconstructed presentation morphism recovers the natural transformation. -/
theorem toNatTrans_ofNatTrans {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) : toNatTrans (ofNatTrans α) = α := sorry

/-- Presentation morphisms correspond to natural transformations of groupoid-valued functors. -/
def equivToNatTrans (G H : GroupoidInFunctors.{u, v, w} C) :
    Hom G H ≃ (G.toFunctor ⟶ H.toFunctor) where
  toFun := toNatTrans
  invFun := ofNatTrans
  left_inv := ofNatTrans_toNatTrans
  right_inv := toNatTrans_ofNatTrans

/-- The morphism correspondence evaluates by taking the induced natural transformation. -/
theorem equivToNatTrans_apply {G H : GroupoidInFunctors.{u, v, w} C} (f : Hom G H) :
    equivToNatTrans G H f = toNatTrans f := rfl

/-- The inverse morphism correspondence evaluates by reconstructing a presentation morphism. -/
theorem equivToNatTrans_symm_apply {G H : GroupoidInFunctors.{u, v, w} C}
    (α : G.toFunctor ⟶ H.toFunctor) :
    (equivToNatTrans G H).symm α = ofNatTrans α := rfl

end Hom

namespace FromFunctor

variable (F : C ⥤ Grpd.{w, w})

set_option backward.privateInPublic true in
@[expose] private def arrowCarrier (T : C) : Type w :=
  Σ x : F.obj T, Σ y : F.obj T, (x ⟶ y)

set_option backward.privateInPublic true in
@[expose] private def arrowMap {T T' : C} (transition : T ⟶ T') :
    arrowCarrier F T → arrowCarrier F T' :=
  fun arrow ↦ ⟨(F.map transition).obj arrow.1, (F.map transition).obj arrow.2.1,
    (F.map transition).map arrow.2.2⟩

/-- The transition on endpoint-indexed arrows preserves identity base morphisms. -/
private theorem arrowFunctor_map_id (T : C) :
    TypeCat.ofHom (arrowMap F (𝟙 T)) = 𝟙 (arrowCarrier F T) := sorry

/-- The transition on endpoint-indexed arrows preserves composition of base morphisms. -/
private theorem arrowFunctor_map_comp {T T' T'' : C}
    (first : T ⟶ T') (second : T' ⟶ T'') :
    TypeCat.ofHom (arrowMap F (first ≫ second)) =
      TypeCat.ofHom (arrowMap F first) ≫ TypeCat.ofHom (arrowMap F second) := sorry

set_option backward.privateInPublic true in
@[expose] private def arrowFunctor : C ⥤ Type w where
  obj T := arrowCarrier F T
  map transition := TypeCat.ofHom (arrowMap F transition)
  map_id := private arrowFunctor_map_id F
  map_comp := private fun first second ↦ arrowFunctor_map_comp F first second

/-- Taking the source endpoint commutes with base transitions. -/
private theorem source_naturality {T T' : C} (transition : T ⟶ T') :
    (arrowFunctor F).map transition ≫ TypeCat.ofHom (fun arrow ↦ arrow.1) =
      TypeCat.ofHom (fun arrow ↦ arrow.1) ≫ (F ⋙ Grpd.objects).map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def source : arrowFunctor F ⟶ F ⋙ Grpd.objects where
  app T := TypeCat.ofHom fun arrow ↦ arrow.1
  naturality := private fun _ _ transition ↦ source_naturality F transition

/-- Taking the target endpoint commutes with base transitions. -/
private theorem target_naturality {T T' : C} (transition : T ⟶ T') :
    (arrowFunctor F).map transition ≫ TypeCat.ofHom (fun arrow ↦ arrow.2.1) =
      TypeCat.ofHom (fun arrow ↦ arrow.2.1) ≫ (F ⋙ Grpd.objects).map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def target : arrowFunctor F ⟶ F ⋙ Grpd.objects where
  app T := TypeCat.ofHom fun arrow ↦ arrow.2.1
  naturality := private fun _ _ transition ↦ target_naturality F transition

set_option backward.privateInPublic true in
@[expose] private def compositionApp (T : C) :
    (pullback (source F) (target F)).obj T → (arrowFunctor F).obj T :=
  fun composable ↦
    let pair := (Types.pullbackIsoPullback ((source F).app T) ((target F).app T)).hom
      ((pullbackObjIso (source F) (target F) T).hom composable)
    ⟨pair.val.2.1, pair.val.1.2.1,
      pair.val.2.2.2 ≫ eqToHom pair.property.symm ≫ pair.val.1.2.2⟩

/-- Composition of endpoint-indexed arrows commutes with base transitions. -/
private theorem composition_naturality {T T' : C} (transition : T ⟶ T') :
    (pullback (source F) (target F)).map transition ≫
        TypeCat.ofHom (compositionApp F T') =
      TypeCat.ofHom (compositionApp F T) ≫ (arrowFunctor F).map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def composition : pullback (source F) (target F) ⟶ arrowFunctor F where
  app T := TypeCat.ofHom (compositionApp F T)
  naturality := private fun _ _ transition ↦ composition_naturality F transition

/-- Assigning identity arrows commutes with base transitions. -/
private theorem identity_naturality {T T' : C} (transition : T ⟶ T') :
    (F ⋙ Grpd.objects).map transition ≫
        TypeCat.ofHom (fun x : F.obj T' ↦ (⟨x, x, 𝟙 x⟩ : arrowCarrier F T')) =
      TypeCat.ofHom (fun x : F.obj T ↦ (⟨x, x, 𝟙 x⟩ : arrowCarrier F T)) ≫
        (arrowFunctor F).map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def identity : F ⋙ Grpd.objects ⟶ arrowFunctor F where
  app T := TypeCat.ofHom fun x : F.obj T ↦ ⟨x, x, 𝟙 x⟩
  naturality := private fun _ _ transition ↦ identity_naturality F transition

/-- Inverting endpoint-indexed arrows commutes with base transitions. -/
private theorem inverse_naturality {T T' : C} (transition : T ⟶ T') :
    (arrowFunctor F).map transition ≫
        TypeCat.ofHom (fun arrow : arrowCarrier F T' ↦
          (⟨arrow.2.1, arrow.1, Groupoid.inv arrow.2.2⟩ : arrowCarrier F T')) =
      TypeCat.ofHom (fun arrow : arrowCarrier F T ↦
          (⟨arrow.2.1, arrow.1, Groupoid.inv arrow.2.2⟩ : arrowCarrier F T)) ≫
        (arrowFunctor F).map transition := sorry

set_option backward.privateInPublic true in
@[expose] private def inverse : arrowFunctor F ⟶ arrowFunctor F where
  app T := TypeCat.ofHom fun arrow ↦ ⟨arrow.2.1, arrow.1, Groupoid.inv arrow.2.2⟩
  naturality := private fun _ _ transition ↦ inverse_naturality F transition

/-- The source of a composite is the source of the earlier arrow. -/
private theorem comp_source :
    composition F ≫ source F = pullback.snd (source F) (target F) ≫ source F := sorry

/-- The target of a composite is the target of the later arrow. -/
private theorem comp_target :
    composition F ≫ target F = pullback.fst (source F) (target F) ≫ target F := sorry

/-- The source of an identity arrow is its object. -/
private theorem identity_source : identity F ≫ source F = 𝟙 (F ⋙ Grpd.objects) := sorry

/-- The target of an identity arrow is its object. -/
private theorem identity_target : identity F ≫ target F = 𝟙 (F ⋙ Grpd.objects) := sorry

/-- The source of an inverse arrow is the target of the original arrow. -/
private theorem inverse_source : inverse F ≫ source F = target F := sorry

/-- The target of an inverse arrow is the source of the original arrow. -/
private theorem inverse_target : inverse F ≫ target F = source F := sorry

/-- Composition of generalized endpoint-indexed arrows is associative. -/
private theorem associativity {W : C ⥤ Type w} (a b d : W ⟶ arrowFunctor F)
    (h_ab : a ≫ source F = b ≫ target F) (h_bd : b ≫ source F = d ≫ target F)
    (h_ab_d : (pullback.lift a b h_ab ≫ composition F) ≫ source F = d ≫ target F)
    (h_a_bd : a ≫ source F = (pullback.lift b d h_bd ≫ composition F) ≫ target F) :
    pullback.lift (pullback.lift a b h_ab ≫ composition F) d h_ab_d ≫ composition F =
      pullback.lift a (pullback.lift b d h_bd ≫ composition F) h_a_bd ≫ composition F := sorry

/-- Composing an arrow with the identity at its source leaves it unchanged. -/
private theorem right_identity {W : C ⥤ Type w} (a : W ⟶ arrowFunctor F)
    (h : a ≫ source F = ((a ≫ source F) ≫ identity F) ≫ target F) :
    pullback.lift a ((a ≫ source F) ≫ identity F) h ≫ composition F = a := sorry

/-- Composing the identity at the target with an arrow leaves it unchanged. -/
private theorem left_identity {W : C ⥤ Type w} (a : W ⟶ arrowFunctor F)
    (h : ((a ≫ target F) ≫ identity F) ≫ source F = a ≫ target F) :
    pullback.lift ((a ≫ target F) ≫ identity F) a h ≫ composition F = a := sorry

/-- Composing an arrow after its inverse yields the identity at its target. -/
private theorem inverse_comp {W : C ⥤ Type w} (a : W ⟶ arrowFunctor F)
    (h : a ≫ source F = (a ≫ inverse F) ≫ target F) :
    pullback.lift a (a ≫ inverse F) h ≫ composition F = (a ≫ target F) ≫ identity F := sorry

/-- Composing an inverse after its arrow yields the identity at its source. -/
private theorem comp_inverse {W : C ⥤ Type w} (a : W ⟶ arrowFunctor F)
    (h : (a ≫ inverse F) ≫ source F = a ≫ target F) :
    pullback.lift (a ≫ inverse F) a h ≫ composition F = (a ≫ source F) ≫ identity F := sorry

end FromFunctor

set_option backward.privateInPublic true in
/-- Present a groupoid-valued functor using its objects and endpoint-indexed arrows. -/
def ofFunctor (F : C ⥤ Grpd.{w, w}) : GroupoidInFunctors.{u, v, w} C where
  U := F ⋙ Grpd.objects
  R := FromFunctor.arrowFunctor F
  s := FromFunctor.source F
  t := FromFunctor.target F
  c := FromFunctor.composition F
  e := FromFunctor.identity F
  i := FromFunctor.inverse F
  comp_source := private FromFunctor.comp_source F
  comp_target := private FromFunctor.comp_target F
  identity_source := private FromFunctor.identity_source F
  identity_target := private FromFunctor.identity_target F
  inverse_source := private FromFunctor.inverse_source F
  inverse_target := private FromFunctor.inverse_target F
  associativity := private fun a b d h_ab h_bd h_ab_d h_a_bd ↦
    FromFunctor.associativity F a b d h_ab h_bd h_ab_d h_a_bd
  right_identity := private fun a compatible ↦ FromFunctor.right_identity F a compatible
  left_identity := private fun a compatible ↦ FromFunctor.left_identity F a compatible
  inverse_comp := private fun a compatible ↦ FromFunctor.inverse_comp F a compatible
  comp_inverse := private fun a compatible ↦ FromFunctor.comp_inverse F a compatible

/-- Reconstruction has exactly the supplied object functor. -/
theorem ofFunctor_U (F : C ⥤ Grpd.{w, w}) : (ofFunctor F).U = F ⋙ Grpd.objects := rfl

/-- The reconstructed arrows are all fibre arrows with their source and target endpoints. -/
theorem ofFunctor_R_obj (F : C ⥤ Grpd.{w, w}) (T : C) :
    (ofFunctor F).R.obj T = (Σ x : F.obj T, Σ y : F.obj T, (x ⟶ y)) := rfl

namespace FromFunctor

variable (F : C ⥤ Grpd.{w, w}) (T : C)

set_option backward.privateInPublic true in
@[expose] private def unpack {x y : F.obj T} (arrow : (ofFunctor F).PointHom T x y) :
    (x ⟶ y) :=
  eqToHom arrow.source.symm ≫ arrow.arrow.2.2 ≫ eqToHom arrow.target

set_option backward.privateInPublic true in
@[expose] private def pack {x y : F.obj T} (arrow : x ⟶ y) : (ofFunctor F).PointHom T x y :=
  PointHom.ofArrow ⟨x, y, arrow⟩ rfl rfl

/-- Unpacking a pointwise identity gives the original groupoid identity. -/
private theorem fromPoints_map_id (x : F.obj T) :
    unpack F T (PointHom.id (ofFunctor F) T x) = 𝟙 x := sorry

/-- Unpacking pointwise composition gives composition in the original groupoid. -/
private theorem fromPoints_map_comp {x y z : F.obj T}
    (earlier : (ofFunctor F).PointHom T x y) (later : (ofFunctor F).PointHom T y z) :
    unpack F T (PointHom.comp earlier later) = unpack F T earlier ≫ unpack F T later := sorry

set_option backward.privateInPublic true in
@[expose] private def fromPoints : (ofFunctor F).groupoidPoints T ⥤ F.obj T where
  obj x := x
  map := fun arrow ↦ unpack F T arrow
  map_id := private fromPoints_map_id F T
  map_comp := private fun earlier later ↦ fromPoints_map_comp F T earlier later

/-- Packing an identity arrow gives the identity of the reconstructed point groupoid. -/
private theorem toPoints_map_id (x : F.obj T) :
    pack F T (𝟙 x) = PointHom.id (ofFunctor F) T x := sorry

/-- Packing a composite gives composition in the reconstructed point groupoid. -/
private theorem toPoints_map_comp {x y z : F.obj T} (earlier : x ⟶ y) (later : y ⟶ z) :
    pack F T (earlier ≫ later) = PointHom.comp (pack F T earlier) (pack F T later) := sorry

set_option backward.privateInPublic true in
@[expose] private def toPoints : F.obj T ⥤ (ofFunctor F).groupoidPoints T where
  obj x := x
  map := fun arrow ↦ pack F T arrow
  map_id := private toPoints_map_id F T
  map_comp := private fun earlier later ↦ toPoints_map_comp F T earlier later

/-- Packing after unpacking is the identity functor of the reconstructed groupoid. -/
private theorem pointIso_hom_inv_id :
    fromPoints F T ≫ toPoints F T = 𝟙 ((ofFunctor F).groupoidPoints T) := sorry

/-- Unpacking after packing is the identity functor of the supplied groupoid. -/
private theorem pointIso_inv_hom_id :
    toPoints F T ≫ fromPoints F T = 𝟙 (F.obj T) := sorry

set_option backward.privateInPublic true in
@[expose] private def pointIso : (ofFunctor F).toFunctor.obj T ≅ F.obj T where
  hom := fromPoints F T
  inv := toPoints F T
  hom_inv_id := private pointIso_hom_inv_id F T
  inv_hom_id := private pointIso_inv_hom_id F T

/-- The fibre recovery isomorphisms commute with base transitions. -/
private theorem pointIso_naturality {T T' : C} (transition : T ⟶ T') :
    (ofFunctor F).toFunctor.map transition ≫ (pointIso F T').hom =
      (pointIso F T).hom ≫ F.map transition := sorry

end FromFunctor

set_option backward.privateInPublic true in
/-- Evaluating the reconstructed presentation recovers the supplied groupoid-valued functor. -/
def toFunctorOfFunctorIso (F : C ⥤ Grpd.{w, w}) : (ofFunctor F).toFunctor ≅ F :=
  NatIso.ofComponents (FromFunctor.pointIso F)
    (by
      intro T T' transition
      exact FromFunctor.pointIso_naturality F transition)

/-- The recovery isomorphism is the identity on every fibre's objects. -/
theorem toFunctorOfFunctorIso_hom_app_obj (F : C ⥤ Grpd.{w, w}) (T : C)
    (x : (ofFunctor F).U.obj T) : ((toFunctorOfFunctorIso F).hom.app T).obj x = x := rfl

end CategoryTheory.GroupoidInFunctors
