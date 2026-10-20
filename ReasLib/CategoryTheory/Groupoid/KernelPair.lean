module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Groupoid.InFunctors
public import ReasLib.CategoryTheory.Cofibered.Grothendieck

/-!
# Kernel-pair groupoids of morphisms to cofibered groupoid categories
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory Limits Functor TypeCat
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

/-- The image of an element in the total category of a cofibered groupoid category. -/
def imageObj (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T) : F.total :=
  (CofiberedCategoryOver.Groupoids.toFunctor f).obj ⟨T, x⟩

private def elementsArrow {T T' : C} (φ : T ⟶ T') (x : U.obj T) :
    { g : T ⟶ T' // U.map g x = U.map φ x } := ⟨φ, rfl⟩

/-- The image of the category-of-elements transition over a base morphism. -/
def imageLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (x : U.obj T) :
    imageObj f T x ⟶ imageObj f T' (U.map φ x) :=
  (CofiberedCategoryOver.Groupoids.toFunctor f).map (elementsArrow φ x)

/-- The image of an element lies over the base object of that element. -/
theorem imageObj_base (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T) :
    F.p.obj (imageObj f T x) = T :=
  congrArg (fun G ↦ G.obj ⟨T, x⟩) (CofiberedCategoryOver.Groupoids.comm f)

/-- The identity of an image object lifts the identity of its base object. -/
theorem imageObj_id_isHomLift (f : Functor.ofTypeValued U ⟶ F) (T : C)
    (x : U.obj T) : F.p.IsHomLift (𝟙 T) (𝟙 (imageObj f T x)) :=
  IsHomLift.id (imageObj_base f T x)

/-- The image of an elements transition lifts its base morphism. -/
theorem imageLift_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C}
    (φ : T ⟶ T') (x : U.obj T) : F.p.IsHomLift φ (imageLift f φ x) := by
  exact IsHomLift.of_fac' F.p φ (imageLift f φ x)
    (imageObj_base f T x) (imageObj_base f T' (U.map φ x))
    (Functor.congr_hom (CofiberedCategoryOver.Groupoids.comm f)
      (X := ⟨T, x⟩) (Y := ⟨T', U.map φ x⟩) (elementsArrow φ x))

private theorem homLift_op {S : Type*} [Category S] (projection : S ⥤ C)
    {T T' : C} {first last : S} {base : T ⟶ T'} {arrow : first ⟶ last}
    (lift : projection.IsHomLift base arrow) :
    projection.op.IsHomLift base.op arrow.op := by
  cases lift
  exact .map _

private theorem homLift_unop {S : Type*} [Category S] (projection : S ⥤ C)
    {T T' : Cᵒᵖ} {first last : Sᵒᵖ} {base : T ⟶ T'} {arrow : first ⟶ last}
    (lift : projection.op.IsHomLift base arrow) :
    projection.IsHomLift base.unop arrow.unop := by
  cases lift
  exact .map _

private theorem stronglyCocartesian {S : Type*} [Category S] (projection : S ⥤ C)
    [IsFibered.InGroupoids projection.op] {first last : S} (arrow : first ⟶ last) :
    projection.IsStronglyCocartesian (projection.map arrow) arrow where
  toIsHomLift := .map _
  universal_property' := by
    intro other base composite lift
    have cartesian : projection.op.IsStronglyCartesian (projection.map arrow).op arrow.op :=
      @IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ projection.op
        (IsFibered.InGroupoids.toIsFibered (self := inferInstance)) _ _ _ _ _ arrow.op
        (IsFibered.InGroupoids.all_isCartesian arrow.op)
    obtain ⟨factor, ⟨factorLift, factorization⟩, unique⟩ :=
      @IsStronglyCartesian.universal_property' _ _ _ _ projection.op _ _ _ _ _ _ cartesian
        _ base.op composite.op (homLift_op projection lift)
    refine ⟨factor.unop, ⟨homLift_unop projection factorLift, ?_⟩, ?_⟩
    · exact congrArg Quiver.Hom.unop factorization
    · intro candidate specification
      have equality := unique candidate.op
        ⟨homLift_op projection specification.1,
          congrArg Quiver.Hom.op specification.2⟩
      exact congrArg Quiver.Hom.unop equality

private theorem stronglyCocartesian_of_lift {S : Type*} [Category S] (projection : S ⥤ C)
    [IsFibered.InGroupoids projection.op] {first last : S} {T T' : C}
    (base : T ⟶ T') (arrow : first ⟶ last) (lift : projection.IsHomLift base arrow) :
    projection.IsStronglyCocartesian base arrow := by
  cases lift
  exact stronglyCocartesian projection arrow

/-- The image transition is strongly cocartesian over its base morphism. -/
theorem imageLift_isStronglyCocartesian (f : Functor.ofTypeValued U ⟶ F) {T T' : C}
    (φ : T ⟶ T') (x : U.obj T) : F.p.IsStronglyCocartesian φ (imageLift f φ x) := by
  exact stronglyCocartesian_of_lift F.p φ (imageLift f φ x)
    (imageLift_isHomLift f φ x)

/-- A vertical morphism followed by an image transition lifts the transition's base map. -/
theorem imageLift_comp_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C}
    (φ : T ⟶ T') {x y : U.obj T} (arrow : imageObj f T x ⟶ imageObj f T y)
    (lift : F.p.IsHomLift (𝟙 T) arrow) : F.p.IsHomLift φ (arrow ≫ imageLift f φ y) :=
  @IsHomLift.comp_lift_id_left _ _ _ _ F.p _ _ _ _ _ φ (imageLift f φ y)
    (imageLift_isHomLift f φ y) arrow lift

/-- An arrow of the kernel pair: a pair of objects of `U` together with an isomorphism of
their images in the fibre of `F`. -/
structure Arrow (f : Functor.ofTypeValued U ⟶ F) (T : C) where
  /-- The first factor, which is the target of the arrow. -/
  left : U.obj T
  /-- The second factor, which is the source of the arrow. -/
  right : U.obj T
  /-- The forward isomorphism of images in `F`. -/
  hom : imageObj f T left ⟶ imageObj f T right
  /-- The inverse isomorphism of images in `F`. -/
  inv : imageObj f T right ⟶ imageObj f T left
  /-- `hom` and `inv` are inverse. -/
  hom_inv_id : hom ≫ inv = 𝟙 (imageObj f T left)
  /-- `inv` and `hom` are inverse. -/
  inv_hom_id : inv ≫ hom = 𝟙 (imageObj f T right)
  /-- `hom` lies over the identity of `T`. -/
  hom_isHomLift : F.p.IsHomLift (𝟙 T) hom
  /-- `inv` lies over the identity of `T`. -/
  inv_isHomLift : F.p.IsHomLift (𝟙 T) inv

namespace Arrow

/-- Composing the forward and inverse identity maps gives the identity. -/
theorem id_hom_inv_id (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) :
    (𝟙 (imageObj f T x)) ≫ 𝟙 (imageObj f T x) = 𝟙 (imageObj f T x) := sorry

/-- Composing the inverse and forward identity maps gives the identity. -/
theorem id_inv_hom_id (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) :
    (𝟙 (imageObj f T x)) ≫ 𝟙 (imageObj f T x) = 𝟙 (imageObj f T x) := sorry

/-- The forward identity map lies over the identity of the base object. -/
theorem id_hom_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) :
    F.p.IsHomLift (𝟙 T) (𝟙 (imageObj f T x)) := sorry

/-- The inverse identity map lies over the identity of the base object. -/
theorem id_inv_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) :
    F.p.IsHomLift (𝟙 T) (𝟙 (imageObj f T x)) := sorry

/-- The identity arrow on an object of the object functor. -/
def id (f : Functor.ofTypeValued U ⟶ F) {T : C} (x : U.obj T) : Arrow f T where
  left := x
  right := x
  hom := 𝟙 (imageObj f T x)
  inv := 𝟙 (imageObj f T x)
  hom_inv_id := id_hom_inv_id f x
  inv_hom_id := id_inv_hom_id f x
  hom_isHomLift := id_hom_isHomLift f x
  inv_isHomLift := id_inv_isHomLift f x

/-- The inverse of a kernel-pair arrow. -/
def inverse {f : Functor.ofTypeValued U ⟶ F} {T : C} (a : Arrow f T) : Arrow f T where
  left := a.right
  right := a.left
  hom := a.inv
  inv := a.hom
  hom_inv_id := a.inv_hom_id
  inv_hom_id := a.hom_inv_id
  hom_isHomLift := a.inv_isHomLift
  inv_isHomLift := a.hom_isHomLift

/-- The composite forward map followed by its inverse is the identity. -/
theorem comp_hom_inv_id {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) :
    (later.hom ≫ eqToHom (congrArg (imageObj f T) h) ≫ earlier.hom) ≫ (earlier.inv ≫ eqToHom (congrArg (imageObj f T) h.symm) ≫ later.inv) = 𝟙 (imageObj f T later.left) := sorry

/-- The composite inverse map followed by its forward map is the identity. -/
theorem comp_inv_hom_id {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) :
    (earlier.inv ≫ eqToHom (congrArg (imageObj f T) h.symm) ≫ later.inv) ≫ (later.hom ≫ eqToHom (congrArg (imageObj f T) h) ≫ earlier.hom) = 𝟙 (imageObj f T earlier.right) := sorry

/-- The forward composite of two vertical isomorphisms is vertical. -/
theorem comp_hom_isHomLift {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) :
    F.p.IsHomLift (𝟙 T) (later.hom ≫ eqToHom (congrArg (imageObj f T) h) ≫ earlier.hom) := sorry

/-- The inverse composite of two vertical isomorphisms is vertical. -/
theorem comp_inv_isHomLift {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) :
    F.p.IsHomLift (𝟙 T) (earlier.inv ≫ eqToHom (congrArg (imageObj f T) h.symm) ≫ later.inv) := sorry

/-- Composition of two kernel-pair arrows with matching endpoints. -/
def comp {f : Functor.ofTypeValued U ⟶ F} {T : C} (later earlier : Arrow f T)
    (h : later.right = earlier.left) : Arrow f T where
  left := later.left
  right := earlier.right
  hom := later.hom ≫ eqToHom (congrArg (imageObj f T) h) ≫ earlier.hom
  inv := earlier.inv ≫ eqToHom (congrArg (imageObj f T) h.symm) ≫ later.inv
  hom_inv_id := comp_hom_inv_id later earlier h
  inv_hom_id := comp_inv_hom_id later earlier h
  hom_isHomLift := comp_hom_isHomLift later earlier h
  inv_isHomLift := comp_inv_isHomLift later earlier h

/-- Transport a morphism of images in `F` along a base arrow, using the strongly cocartesian
lift of the image of the unique elements-arrow. -/
private def transportHom (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T')
    {x y : U.obj T} (α : imageObj f T x ⟶ imageObj f T y)
    (hSC : F.p.IsStronglyCocartesian φ (imageLift f φ x))
    (hLift : F.p.IsHomLift φ (α ≫ imageLift f φ y)) :
    imageObj f T' (U.map φ x) ⟶ imageObj f T' (U.map φ y) :=
  @IsStronglyCocartesian.map _ _ _ _ F.p _ _ (imageObj f T x) (imageObj f T' (U.map φ x))
    φ (imageLift f φ x) hSC _ (imageObj f T' (U.map φ y)) (𝟙 T') φ
    (Category.comp_id φ).symm (α ≫ imageLift f φ y) hLift

private theorem transportHom_fac (f : Functor.ofTypeValued U ⟶ F) {T T' : C}
    (φ : T ⟶ T') {x y : U.obj T} (α : imageObj f T x ⟶ imageObj f T y)
    (cocartesian : F.p.IsStronglyCocartesian φ (imageLift f φ x))
    (lift : F.p.IsHomLift φ (α ≫ imageLift f φ y)) :
    imageLift f φ x ≫ transportHom f φ α cocartesian lift = α ≫ imageLift f φ y :=
  @IsStronglyCocartesian.fac _ _ _ _ F.p _ _ _ _ _ _ cocartesian _ _ _ _
    (Category.comp_id φ).symm (α ≫ imageLift f φ y) lift

/-- The transported forward map followed by its transported inverse is the identity. -/
theorem map_hom_inv_id (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    (transportHom f φ a.hom (imageLift_isStronglyCocartesian f φ a.left) (imageLift_comp_isHomLift f φ a.hom a.hom_isHomLift)) ≫ (transportHom f φ a.inv (imageLift_isStronglyCocartesian f φ a.right) (imageLift_comp_isHomLift f φ a.inv a.inv_isHomLift)) = 𝟙 (imageObj f T' (U.map φ a.left)) := sorry

/-- The transported inverse map followed by its transported forward map is the identity. -/
theorem map_inv_hom_id (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    (transportHom f φ a.inv (imageLift_isStronglyCocartesian f φ a.right) (imageLift_comp_isHomLift f φ a.inv a.inv_isHomLift)) ≫ (transportHom f φ a.hom (imageLift_isStronglyCocartesian f φ a.left) (imageLift_comp_isHomLift f φ a.hom a.hom_isHomLift)) = 𝟙 (imageObj f T' (U.map φ a.right)) := sorry

/-- The transported forward map lies over the identity at the new base object. -/
theorem map_hom_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    F.p.IsHomLift (𝟙 T') (transportHom f φ a.hom (imageLift_isStronglyCocartesian f φ a.left) (imageLift_comp_isHomLift f φ a.hom a.hom_isHomLift)) := sorry

/-- The transported inverse map lies over the identity at the new base object. -/
theorem map_inv_isHomLift (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    F.p.IsHomLift (𝟙 T') (transportHom f φ a.inv (imageLift_isStronglyCocartesian f φ a.right) (imageLift_comp_isHomLift f φ a.inv a.inv_isHomLift)) := sorry

/-- Transport of a kernel-pair arrow along a base morphism. -/
def map (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') (a : Arrow f T) :
    Arrow f T' where
  left := U.map φ a.left
  right := U.map φ a.right
  hom := transportHom f φ a.hom (imageLift_isStronglyCocartesian f φ a.left)
    (imageLift_comp_isHomLift f φ a.hom a.hom_isHomLift)
  inv := transportHom f φ a.inv (imageLift_isStronglyCocartesian f φ a.right)
    (imageLift_comp_isHomLift f φ a.inv a.inv_isHomLift)
  hom_inv_id := map_hom_inv_id f φ a
  inv_hom_id := map_inv_hom_id f φ a
  hom_isHomLift := map_hom_isHomLift f φ a
  inv_isHomLift := map_inv_isHomLift f φ a

end Arrow

/-- Transport of kernel-pair arrows preserves identities. -/
theorem relation_map_id (f : Functor.ofTypeValued U ⟶ F) (T : C) :
    ofHom (fun a ↦ Arrow.map f (𝟙 T) a) = 𝟙 (Arrow f T) := sorry

/-- Transport of kernel-pair arrows preserves composition. -/
theorem relation_map_comp (f : Functor.ofTypeValued U ⟶ F) {T T' T'' : C} (first : T ⟶ T') (second : T' ⟶ T'') :
    ofHom (fun a ↦ Arrow.map f (first ≫ second) a) =
      ofHom (fun a ↦ Arrow.map f first a) ≫ ofHom (fun a ↦ Arrow.map f second a) := sorry

/-- The Type-valued functor `R = U ×_{f, F, f} U`. -/
def relation (f : Functor.ofTypeValued U ⟶ F) : C ⥤ Type (max v w) where
  obj T := Arrow f T
  map φ := ofHom fun a ↦ Arrow.map f φ a
  map_id := relation_map_id f
  map_comp := fun {_ _ _} first second ↦ relation_map_comp f first second

/-- The left endpoint commutes with transport. -/
theorem tgt_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (relation f).map φ ≫ ofHom (fun a ↦ a.left) =
      ofHom (fun a ↦ a.left) ≫ U.map φ := sorry

/-- The target projection, sending an arrow to its first factor. -/
def tgt (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ U where
  app T := ofHom fun a ↦ a.left
  naturality := fun {_ _} φ ↦ tgt_naturality f φ

/-- The right endpoint commutes with transport. -/
theorem src_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (relation f).map φ ≫ ofHom (fun a ↦ a.right) =
      ofHom (fun a ↦ a.right) ≫ U.map φ := sorry

/-- The source projection, sending an arrow to its second factor. -/
def src (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ U where
  app T := ofHom fun a ↦ a.right
  naturality := fun {_ _} φ ↦ src_naturality f φ

/-- A triple of objects of `U` with composable kernel-pair isomorphisms, modelling
`U ×_F U ×_F U`. -/
structure Triple (f : Functor.ofTypeValued U ⟶ F) (T : C) where
  /-- The first factor. -/
  left : U.obj T
  /-- The middle factor. -/
  middle : U.obj T
  /-- The last factor. -/
  right : U.obj T
  /-- The isomorphism from the first image to the middle image. -/
  iso₀ : Arrow f T
  /-- The isomorphism from the middle image to the last image. -/
  iso₁ : Arrow f T
  /-- `iso₀` has first factor `left`. -/
  iso₀_left : iso₀.left = left
  /-- `iso₀` has second factor `middle`. -/
  iso₀_right : iso₀.right = middle
  /-- `iso₁` has first factor `middle`. -/
  iso₁_left : iso₁.left = middle
  /-- `iso₁` has second factor `right`. -/
  iso₁_right : iso₁.right = right

/-- Two arrows whose adjacent endpoints match determine a triple of elements. -/
def Triple.ofComposable {f : Functor.ofTypeValued U ⟶ F} {T : C}
    (later earlier : Arrow f T) (matching : later.right = earlier.left) : Triple f T where
  left := later.left
  middle := later.right
  right := earlier.right
  iso₀ := later
  iso₁ := earlier
  iso₀_left := rfl
  iso₀_right := rfl
  iso₁_left := matching.symm
  iso₁_right := rfl

private def tripleMap (f : Functor.ofTypeValued U ⟶ F) {T T' : C}
    (φ : T ⟶ T') (point : Triple f T) : Triple f T' where
  left := U.map φ point.left
  middle := U.map φ point.middle
  right := U.map φ point.right
  iso₀ := Arrow.map f φ point.iso₀
  iso₁ := Arrow.map f φ point.iso₁
  iso₀_left := congrArg (fun x ↦ U.map φ x) point.iso₀_left
  iso₀_right := congrArg (fun x ↦ U.map φ x) point.iso₀_right
  iso₁_left := congrArg (fun x ↦ U.map φ x) point.iso₁_left
  iso₁_right := congrArg (fun x ↦ U.map φ x) point.iso₁_right

/-- Transport of triples preserves identities. -/
theorem triple_map_id (f : Functor.ofTypeValued U ⟶ F) (T : C) :
    ofHom (fun point ↦ tripleMap f (𝟙 T) point) = 𝟙 (Triple f T) := sorry

/-- Transport of triples preserves composition. -/
theorem triple_map_comp (f : Functor.ofTypeValued U ⟶ F) {T T' T'' : C}
    (first : T ⟶ T') (second : T' ⟶ T'') :
    ofHom (fun point ↦ tripleMap f (first ≫ second) point) =
      ofHom (fun point ↦ tripleMap f first point) ≫
        ofHom (fun point ↦ tripleMap f second point) := sorry

/-- The Type-valued functor of triples `U ×_{f, F, f} U ×_{f, F, f} U`. -/
def triple (f : Functor.ofTypeValued U ⟶ F) : C ⥤ Type (max v w) where
  obj T := Triple f T
  map φ := ofHom fun point ↦ tripleMap f φ point
  map_id := triple_map_id f
  map_comp := fun {_ _ _} first second ↦ triple_map_comp f first second

/-- Extract a composable triple from a point of the pullback of `src` against `tgt`. -/
private def composableToTriple (f : Functor.ofTypeValued U ⟶ F) (T : C)
    (p : (pullback (src f) (tgt f)).obj T) : Triple f T :=
  let e := (Types.pullbackIsoPullback ((src f).app T) ((tgt f).app T)).hom
    ((pullbackObjIso (src f) (tgt f) T).hom p)
  Triple.ofComposable e.1.1 e.1.2 e.2

/-- Rebuild a pullback point from a composable triple. -/
private def tripleToComposable (f : Functor.ofTypeValued U ⟶ F) (T : C)
    (p : Triple f T) : (pullback (src f) (tgt f)).obj T :=
  (pullbackObjIso (src f) (tgt f) T).inv
    ((Types.pullbackIsoPullback ((src f).app T) ((tgt f).app T)).inv
      ⟨⟨p.iso₀, p.iso₁⟩, p.iso₀_right.trans p.iso₁_left.symm⟩)

/-- The pullback-to-triple comparison commutes with base transitions. -/
theorem composableIso_hom_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (pullback (src f) (tgt f)).map φ ≫ ofHom (composableToTriple f T') =
      ofHom (composableToTriple f T) ≫ (triple f).map φ := sorry

/-- The triple-to-pullback comparison commutes with base transitions. -/
theorem composableIso_inv_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (triple f).map φ ≫ ofHom (tripleToComposable f T') =
      ofHom (tripleToComposable f T) ≫ (pullback (src f) (tgt f)).map φ := sorry

/-- Rebuilding a pullback point after extracting its triple is the identity. -/
theorem composableIso_hom_inv_id (f : Functor.ofTypeValued U ⟶ F) :
    ({ app T := ofHom (composableToTriple f T), naturality := fun {_ _} φ ↦ composableIso_hom_naturality f φ } :
      pullback (src f) (tgt f) ⟶ triple f) ≫
    ({ app T := ofHom (tripleToComposable f T), naturality := fun {_ _} φ ↦ composableIso_inv_naturality f φ } : triple f ⟶ pullback (src f) (tgt f)) =
      𝟙 (pullback (src f) (tgt f)) := sorry

/-- Extracting a triple after rebuilding its pullback point is the identity. -/
theorem composableIso_inv_hom_id (f : Functor.ofTypeValued U ⟶ F) :
    ({ app T := ofHom (tripleToComposable f T), naturality := fun {_ _} φ ↦ composableIso_inv_naturality f φ } :
      triple f ⟶ pullback (src f) (tgt f)) ≫
    ({ app T := ofHom (composableToTriple f T), naturality := fun {_ _} φ ↦ composableIso_hom_naturality f φ } : pullback (src f) (tgt f) ⟶ triple f) =
      𝟙 (triple f) := sorry

/-- The canonical isomorphism `R ×_{s, U, t} R ≅ U ×_F U ×_F U`. -/
def composableIso (f : Functor.ofTypeValued U ⟶ F) :
    pullback (src f) (tgt f) ≅ triple f where
  hom :=
    { app T := ofHom fun p ↦ composableToTriple f T p
      naturality := fun {_ _} φ ↦ composableIso_hom_naturality f φ }
  inv :=
    { app T := ofHom fun p ↦ tripleToComposable f T p
      naturality := fun {_ _} φ ↦ composableIso_inv_naturality f φ }
  hom_inv_id := composableIso_hom_inv_id f
  inv_hom_id := composableIso_inv_hom_id f

/-- First-and-last projection commutes with base transitions. -/
theorem firstLast_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (triple f).map φ ≫ ofHom (fun p ↦ Arrow.comp p.iso₀ p.iso₁ (p.iso₀_right.trans p.iso₁_left.symm)) =
      ofHom (fun p ↦ Arrow.comp p.iso₀ p.iso₁ (p.iso₀_right.trans p.iso₁_left.symm)) ≫ (relation f).map φ := sorry

/-- First-and-last projection of a triple onto a kernel-pair arrow. -/
def firstLast (f : Functor.ofTypeValued U ⟶ F) : triple f ⟶ relation f where
  app T := ofHom fun p ↦
    Arrow.comp p.iso₀ p.iso₁ (p.iso₀_right.trans p.iso₁_left.symm)
  naturality := fun {_ _} φ ↦ firstLast_naturality f φ

/-- Composition of kernel-pair arrows: first-and-last projection after `composableIso`. -/
def comp (f : Functor.ofTypeValued U ⟶ F) : pullback (src f) (tgt f) ⟶ relation f :=
  (composableIso f).hom ≫ firstLast f

/-- The identity operation commutes with base transitions. -/
theorem identity_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (U).map φ ≫ ofHom (fun x ↦ Arrow.id f x) =
      ofHom (fun x ↦ Arrow.id f x) ≫ (relation f).map φ := sorry

/-- The identity-arrow map of the kernel pair. -/
def identity (f : Functor.ofTypeValued U ⟶ F) : U ⟶ relation f where
  app T := ofHom fun x ↦ Arrow.id f x
  naturality := fun {_ _} φ ↦ identity_naturality f φ

/-- The inverse operation commutes with base transitions. -/
theorem inverse_naturality (f : Functor.ofTypeValued U ⟶ F) {T T' : C} (φ : T ⟶ T') :
    (relation f).map φ ≫ ofHom (fun a ↦ Arrow.inverse a) =
      ofHom (fun a ↦ Arrow.inverse a) ≫ (relation f).map φ := sorry

/-- The inverse-arrow map of the kernel pair. -/
def inverse (f : Functor.ofTypeValued U ⟶ F) : relation f ⟶ relation f where
  app T := ofHom fun a ↦ Arrow.inverse a
  naturality := fun {_ _} φ ↦ inverse_naturality f φ

/-- The source of a composite is the source of its earlier arrow. -/
theorem ofMorphism_comp_source (f : Functor.ofTypeValued U ⟶ F) :
    (comp f) ≫ (src f) = pullback.snd (src f) (tgt f) ≫ (src f) := sorry

/-- The target of a composite is the target of its later arrow. -/
theorem ofMorphism_comp_target (f : Functor.ofTypeValued U ⟶ F) :
    (comp f) ≫ (tgt f) = pullback.fst (src f) (tgt f) ≫ (tgt f) := sorry

/-- Identity arrows have the specified source. -/
theorem ofMorphism_identity_source (f : Functor.ofTypeValued U ⟶ F) :
    (identity f) ≫ (src f) = 𝟙 U := sorry

/-- Identity arrows have the specified target. -/
theorem ofMorphism_identity_target (f : Functor.ofTypeValued U ⟶ F) :
    (identity f) ≫ (tgt f) = 𝟙 U := sorry

/-- Inversion exchanges source with target. -/
theorem ofMorphism_inverse_source (f : Functor.ofTypeValued U ⟶ F) :
    (inverse f) ≫ (src f) = (tgt f) := sorry

/-- Inversion exchanges target with source. -/
theorem ofMorphism_inverse_target (f : Functor.ofTypeValued U ⟶ F) :
    (inverse f) ≫ (tgt f) = (src f) := sorry

/-- Composition is associative on generalized arrows. -/
theorem ofMorphism_associativity (f : Functor.ofTypeValued U ⟶ F) :
    ∀ {W : C ⥤ Type (max v w)} (a b d : W ⟶ (relation f))
      (h_ab : a ≫ (src f) = b ≫ (tgt f)) (h_bd : b ≫ (src f) = d ≫ (tgt f))
      (h_ab_d : (pullback.lift a b h_ab ≫ (comp f)) ≫ (src f) = d ≫ (tgt f))
      (h_a_bd : a ≫ (src f) = (pullback.lift b d h_bd ≫ (comp f)) ≫ (tgt f)),
      pullback.lift (pullback.lift a b h_ab ≫ (comp f)) d h_ab_d ≫ (comp f) =
        pullback.lift a (pullback.lift b d h_bd ≫ (comp f)) h_a_bd ≫ (comp f) := sorry

/-- Composing an arrow with the identity at its source does not change it. -/
theorem ofMorphism_right_identity (f : Functor.ofTypeValued U ⟶ F) :
    ∀ {W : C ⥤ Type (max v w)} (a : W ⟶ (relation f))
      (h : a ≫ (src f) = ((a ≫ (src f)) ≫ (identity f)) ≫ (tgt f)),
      pullback.lift a ((a ≫ (src f)) ≫ (identity f)) h ≫ (comp f) = a := sorry

/-- Composing the identity at the target of an arrow with that arrow does not change it. -/
theorem ofMorphism_left_identity (f : Functor.ofTypeValued U ⟶ F) :
    ∀ {W : C ⥤ Type (max v w)} (a : W ⟶ (relation f))
      (h : ((a ≫ (tgt f)) ≫ (identity f)) ≫ (src f) = a ≫ (tgt f)),
      pullback.lift ((a ≫ (tgt f)) ≫ (identity f)) a h ≫ (comp f) = a := sorry

/-- Composing an arrow after its inverse gives the identity at its target. -/
theorem ofMorphism_inverse_comp (f : Functor.ofTypeValued U ⟶ F) :
    ∀ {W : C ⥤ Type (max v w)} (a : W ⟶ (relation f))
      (h : a ≫ (src f) = (a ≫ (inverse f)) ≫ (tgt f)),
      pullback.lift a (a ≫ (inverse f)) h ≫ (comp f) = (a ≫ (tgt f)) ≫ (identity f) := sorry

/-- Composing the inverse of an arrow after it gives the identity at its source. -/
theorem ofMorphism_comp_inverse (f : Functor.ofTypeValued U ⟶ F) :
    ∀ {W : C ⥤ Type (max v w)} (a : W ⟶ (relation f))
      (h : (a ≫ (inverse f)) ≫ (src f) = a ≫ (tgt f)),
      pullback.lift (a ≫ (inverse f)) a h ≫ (comp f) = (a ≫ (src f)) ≫ (identity f) := sorry

/-- A morphism from a set-valued functor to a cofibered groupoid category determines
a groupoid in functors with vertical isomorphisms as arrows. -/
noncomputable def ofMorphism (f : Functor.ofTypeValued U ⟶ F) :
    GroupoidInFunctors.{u, v, max v w} C where
  U := U
  R := relation f
  s := src f
  t := tgt f
  c := comp f
  e := identity f
  i := inverse f
  comp_source := ofMorphism_comp_source f
  comp_target := ofMorphism_comp_target f
  identity_source := ofMorphism_identity_source f
  identity_target := ofMorphism_identity_target f
  inverse_source := ofMorphism_inverse_source f
  inverse_target := ofMorphism_inverse_target f
  associativity := ofMorphism_associativity f
  right_identity := ofMorphism_right_identity f
  left_identity := ofMorphism_left_identity f
  inverse_comp := ofMorphism_inverse_comp f
  comp_inverse := ofMorphism_comp_inverse f

/-- The object functor of the kernel-pair groupoid is the given functor `U`. -/
theorem ofMorphism_U (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).U = U := rfl

/-- The arrow functor of the kernel-pair groupoid is `U ×_{f, F, f} U`. -/
theorem ofMorphism_relation (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).R = relation f := rfl

/-- The target map is the first projection of `U ×_{f, F, f} U`. -/
theorem ofMorphism_tgt_eq_fst (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).t = tgt f := rfl

/-- The source map is the second projection of `U ×_{f, F, f} U`. -/
theorem ofMorphism_src_eq_snd (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).s = src f := rfl

/-- Composition is first-and-last projection of the triple product after `composableIso`. -/
theorem ofMorphism_comp_firstLast (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).c = (composableIso f).hom ≫ firstLast f := rfl

end CategoryTheory.GroupoidInFunctors
