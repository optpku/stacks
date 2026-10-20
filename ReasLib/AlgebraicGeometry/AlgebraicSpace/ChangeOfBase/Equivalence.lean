module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Change-of-base equivalence for algebraic spaces

A morphism `g : S ⟶ S'` induces an equivalence between algebraic spaces over `S` and
objects of `Over (ofOver (Over.mk g))`, i.e. algebraic spaces over `S'` equipped with a
morphism to `S` over `S'`. The forward functor is `j_!` together with the canonical
structure morphism; the inverse is the Type `u` fiber of that structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The triangle identity for the structure morphism of `T`, viewed over `S'`. -/
theorem structureIndex_w {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    T.hom ≫ (Over.mk g).hom = ((Over.map g).obj T).hom := sorry

/-- The structure morphism of `T` over `S`, viewed as a morphism `j(T) ⟶ S` over `S'`. -/
def structureIndex {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    (Over.map g).obj T ⟶ Over.mk g :=
  Over.homMk T.hom (structureIndex_w g T)

/-- The underlying scheme morphism of `structureIndex g T` is `T.hom`. -/
@[simp]
theorem structureIndex_left {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    (structureIndex g T).left = T.hom := sorry

/-- Viewing the index of `structureIndex g T` back over `S` recovers `T`. -/
theorem structureIndex_mk {S S' : Scheme.{u}} (g : S ⟶ S') (T : Over S) :
    Over.mk (structureIndex g T).left = T := sorry

/-- The canonical structure morphism `j_! F ⟶ S` of algebraic spaces over `S'`, projecting
the coproduct index of `extendBasePresheaf`. -/
def extendBaseHom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    extendBase g F ⟶ ofOver (Over.mk g) where
  app T' := ofHom fun σ ↦ σ.1
  naturality := fun _ _ _ ↦ sorry

/-- Evaluating `extendBaseHom g F` at `T'` returns the coproduct index. -/
theorem extendBaseHom_app {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T' : Over S'} (φ : T' ⟶ Over.mk g)
    (s : F.functorOfPoints.obj (op (Over.mk φ.left))) :
    (extendBaseHom g F).app (op T') ⟨φ, s⟩ = φ := sorry

/-- A morphism of algebraic spaces over `S` induces a morphism of their extensions to `S'`. -/
def extendBaseMap {S S' : Scheme.{u}} (g : S ⟶ S') {F G : AlgebraicSpace S} (f : F ⟶ G) :
    extendBase g F ⟶ extendBase g G :=
  extendBasePresheafMap g f

/-- Extension of scalars `j_!` as a functor on algebraic spaces. -/
def extendBaseFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ⥤ AlgebraicSpace S' :=
  let laws : (∀ F : AlgebraicSpace S, extendBaseMap g (𝟙 F) = 𝟙 (extendBase g F)) ∧
      (∀ {F G H : AlgebraicSpace S} (f : F ⟶ G) (h : G ⟶ H),
        extendBaseMap g (f ≫ h) = extendBaseMap g f ≫ extendBaseMap g h) := sorry
  { obj := fun F ↦ extendBase g F
    map := fun f ↦ extendBaseMap g f
    map_id := laws.1
    map_comp := laws.2 }

/-- The structure morphisms `extendBaseHom g F` are natural in `F`. -/
theorem extendBaseHom_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : AlgebraicSpace S} (f : F ⟶ G) :
    (extendBaseFunctor g).map f ≫ extendBaseHom g G = extendBaseHom g F := sorry

/-- The comparison functor sending `F` to the object `(j_! F, j_! F ⟶ S)` of the slice. -/
def extendBaseOver {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ⥤ Over (ofOver (Over.mk g)) :=
  (extendBaseFunctor g).toOver (ofOver (Over.mk g)) (extendBaseHom g)
    (extendBaseHom_naturality g)

/-- On objects, `extendBaseOver g` is the slice object of `extendBaseHom g F`. -/
@[simp]
theorem extendBaseOver_obj {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    (extendBaseOver g).obj F = Over.mk (extendBaseHom g F) := sorry

/-- The underlying algebraic space of `(extendBaseOver g).obj F` is `extendBase g F`. -/
@[simp]
theorem extendBaseOver_obj_left {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    ((extendBaseOver g).obj F).left = extendBase g F := sorry

/-- The structure morphism of `(extendBaseOver g).obj F` is `extendBaseHom g F`. -/
@[simp]
theorem extendBaseOver_obj_hom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    ((extendBaseOver g).obj F).hom = extendBaseHom g F := sorry

/-- Sections of `X` over `j(T)` lying over the structure map of `T`. -/
def restrictOverSection {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) (T : Over S) : Type u :=
  { s : X.left.functorOfPoints.obj (op ((Over.map g).obj T)) //
    X.hom.app (op ((Over.map g).obj T)) s = structureIndex g T }

/-- Restriction of a fiber section along a morphism of schemes over `S`. -/
theorem restrictOverSection_map_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T T' : Over S} (f : T' ⟶ T)
    (s : restrictOverSection X T) :
    X.hom.app (op ((Over.map g).obj T'))
        (X.left.functorOfPoints.map ((Over.map g).map f).op s.1) =
      structureIndex g T' := sorry

/-- The inverse functor of points: the Type `u` fiber of `X.hom` over `structureIndex`. -/
def restrictOverPresheaf {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : (Over S)ᵒᵖ ⥤ Type u :=
  let obj := fun T : (Over S)ᵒᵖ ↦ restrictOverSection X T.unop
  let map : ∀ {T T' : (Over S)ᵒᵖ}, (T ⟶ T') → (obj T ⟶ obj T') :=
    fun f ↦ ofHom fun s ↦
      ⟨X.left.functorOfPoints.map ((Over.map g).map f.unop).op s.1,
        restrictOverSection_map_mem X f.unop s⟩
  let laws : (∀ T, map (𝟙 T) = 𝟙 (obj T)) ∧
      (∀ {T T' T'' : (Over S)ᵒᵖ} (f : T ⟶ T') (h : T' ⟶ T''),
        map (f ≫ h) = map f ≫ map h) := sorry
  { obj := obj, map := map, map_id := laws.1, map_comp := laws.2 }

/-- The triangle identifying `j` of the index of `φ : T' ⟶ S` with `T'` itself. -/
theorem viewedIndexIso_w {S S' : Scheme.{u}} {g : S ⟶ S'} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) :
    (Iso.refl ((Over.map g).obj (Over.mk φ.left)).left).hom ≫ T'.hom =
      ((Over.map g).obj (Over.mk φ.left)).hom := sorry

/-- Viewing `T'` over `S` along `φ : T' ⟶ S` and then applying `j = Over.map g` recovers
`T'` up to the slice identification. -/
def viewedIndexIso {S S' : Scheme.{u}} {g : S ⟶ S'} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) :
    (Over.map g).obj (Over.mk φ.left) ≅ T' :=
  let laws : (𝟙 T'.left ≫ ((Over.map g).obj (Over.mk φ.left)).hom = T'.hom) ∧
      (𝟙 T'.left ≫ 𝟙 T'.left = 𝟙 ((Over.map g).obj (Over.mk φ.left)).left) ∧
      (𝟙 T'.left ≫ 𝟙 T'.left = 𝟙 T'.left) := sorry
  { hom := Over.homMk (𝟙 T'.left) (viewedIndexIso_w φ)
    inv := Over.homMk (𝟙 T'.left) laws.1
    hom_inv_id := by
      apply Over.OverMorphism.ext
      exact laws.2.1
    inv_hom_id := by
      apply Over.OverMorphism.ext
      exact laws.2.2 }

/-- The original atlas's structure map to `S`, recovered by native Yoneda fullness. -/
def restrictOverAtlasIndex {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : AtlasInput.scheme X.left ⟶ Over.mk g :=
  yoneda.preimage (AtlasInput.map X.left ≫ X.hom)

/-- The original atlas scheme, viewed over `S` through its actual structure map. -/
def restrictOverAtlas {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : Over S :=
  Over.mk (restrictOverAtlasIndex X).left

/-- Rebasement keeps exactly the original atlas's underlying scheme. -/
@[simp]
theorem restrictOverAtlas_left {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (restrictOverAtlas X).left = (AtlasInput.scheme X.left).left := rfl

/-- The transported original atlas section lies over the new structure map. -/
theorem restrictOverAtlasPoint_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    X.hom.app (op ((Over.map g).obj (restrictOverAtlas X)))
        (X.left.functorOfPoints.map (viewedIndexIso (restrictOverAtlasIndex X)).hom.op
          ((AtlasInput.map X.left).app (op (AtlasInput.scheme X.left)) (𝟙 _))) =
      structureIndex g (restrictOverAtlas X) := sorry

/-- The original atlas point, transported into the actual fibre presheaf. -/
def restrictOverAtlasPoint {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : restrictOverSection X (restrictOverAtlas X) :=
  ⟨X.left.functorOfPoints.map (viewedIndexIso (restrictOverAtlasIndex X)).hom.op
      ((AtlasInput.map X.left).app (op (AtlasInput.scheme X.left)) (𝟙 _)),
    restrictOverAtlasPoint_mem X⟩

/-- The rebased atlas map is the Yoneda map of the transported original atlas point. -/
def restrictOverAtlasMap {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    yoneda.obj (restrictOverAtlas X) ⟶ restrictOverPresheaf X :=
  yonedaEquiv.symm (restrictOverAtlasPoint X)

/-- On each test scheme, the new atlas map is the original atlas map on the same arrow. -/
theorem restrictOverAtlasMap_app_val {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T : Over S} (f : T ⟶ restrictOverAtlas X) :
    ((restrictOverAtlasMap X).app (op T) f).1 =
      (AtlasInput.map X.left).app (op ((Over.map g).obj T))
        ((Over.map g).map f ≫ (viewedIndexIso (restrictOverAtlasIndex X)).hom) := sorry

/-- Restricting an algebraic space over the representable base preserves fppf descent. -/
theorem restrictOver_isSheaf {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictOverPresheaf X) := sorry

namespace RestrictOverDiagonal

variable {S S' : Scheme.{u}} {g : S ⟶ S'} (X : Over (ofOver (Over.mk g)))
variable {T : Over S}
variable (α : yoneda.obj T ⟶ restrictOverPresheaf X ⨯ restrictOverPresheaf X)

/-- The first given fibre section defining the diagonal test. -/
def first : restrictOverSection X T := yonedaEquiv (α ≫ prod.fst)

/-- The second given fibre section defining the diagonal test. -/
def second : restrictOverSection X T := yonedaEquiv (α ≫ prod.snd)

/-- The same pair of sections, considered on the original base. -/
def sourceMap : yoneda.obj ((Over.map g).obj T) ⟶
    X.left.functorOfPoints ⨯ X.left.functorOfPoints :=
  prod.lift (yonedaEquiv.symm (first X α).1) (yonedaEquiv.symm (second X α).1)

/-- The original supplied diagonal certificate supplies this representing scheme. -/
def sourceScheme : Over S' := X.left.representableDiagonal.pullback (sourceMap X α)

def sourceProjection : sourceScheme X α ⟶ (Over.map g).obj T :=
  X.left.representableDiagonal.snd (sourceMap X α)

def sourceIndex : sourceScheme X α ⟶ Over.mk g :=
  sourceProjection X α ≫ structureIndex g T

/-- The same original representing scheme, now over `S`. -/
def scheme : Over S := Over.mk (sourceIndex X α).left

def projection : scheme X α ⟶ T :=
  Over.homMk (sourceProjection X α).left (by rfl)

def sourcePoint : X.left.functorOfPoints.obj (op (sourceScheme X α)) :=
  yonedaEquiv (X.left.representableDiagonal.fst (sourceMap X α))

/-- The original diagonal point has the base structure induced by its projection. -/
theorem point_mem :
    X.hom.app (op ((Over.map g).obj (scheme X α)))
        (X.left.functorOfPoints.map (viewedIndexIso (sourceIndex X α)).hom.op
          (sourcePoint X α)) = structureIndex g (scheme X α) := sorry

def point : restrictOverSection X (scheme X α) :=
  ⟨X.left.functorOfPoints.map (viewedIndexIso (sourceIndex X α)).hom.op
      (sourcePoint X α), point_mem X α⟩

def map : yoneda.obj (scheme X α) ⟶ restrictOverPresheaf X :=
  yonedaEquiv.symm (point X α)

/-- The rebased diagram retains the original two projections. -/
theorem w : map X α ≫ Limits.diag (restrictOverPresheaf X) =
    yoneda.map (projection X α) ≫ α := sorry

/-- A fibre-compatible cone gives an actual cone for the original diagonal. -/
theorem sourceLift_condition {V : Over S} (x : restrictOverSection X V) (f : V ⟶ T)
    (h : (Limits.diag (restrictOverPresheaf X)).app (op V) x = α.app (op V) f) :
    (Limits.diag X.left.functorOfPoints).app (op ((Over.map g).obj V)) x.1 =
      (sourceMap X α).app (op ((Over.map g).obj V)) ((Over.map g).map f) := sorry

/-- The original supplied pullback inverse gives the actual lifted scheme arrow. -/
def sourceLift {V : Over S} (x : restrictOverSection X V) (f : V ⟶ T)
    (h : (Limits.diag (restrictOverPresheaf X)).app (op V) x = α.app (op V) f) :
    (Over.map g).obj V ⟶ sourceScheme X α :=
  (PullbackCone.IsLimit.equivPullbackObj
    ((X.left.representableDiagonal.isPullback (sourceMap X α)).app
      (op ((Over.map g).obj V))).isLimit).symm
    ⟨⟨x.1, (Over.map g).map f⟩, sourceLift_condition X α x f h⟩

theorem liftPoint_mem {V : Over S} (x : restrictOverSection X V) (f : V ⟶ T)
    (h : (Limits.diag (restrictOverPresheaf X)).app (op V) x = α.app (op V) f) :
    (sourceLift X α x f h).left ≫ (scheme X α).hom = V.hom := sorry

/-- The pullback lift is the original lifted arrow, regarded over `S`. -/
def liftPoint {V : Over S} (x : restrictOverSection X V) (f : V ⟶ T)
    (h : (Limits.diag (restrictOverPresheaf X)).app (op V) x = α.app (op V) f) :
    V ⟶ scheme X α :=
  Over.homMk (sourceLift X α x f h).left (liftPoint_mem X α x f h)

/-- The universal lift is assembled pointwise from the supplied original pullback. -/
def lift (s : PullbackCone (Limits.diag (restrictOverPresheaf X)) α) :
    s.pt ⟶ yoneda.obj (scheme X α) where
  app V := ofHom fun x ↦ liftPoint X α (s.fst.app V x) (s.snd.app V x)
    (ConcreteCategory.congr_hom (NatTrans.congr_app s.condition V) x)
  naturality := by sorry

/-- The new pullback stores the explicit lift; only its equations are proof debt. -/
theorem isPullback :
    IsPullback (map X α) (yoneda.map (projection X α))
      (Limits.diag (restrictOverPresheaf X)) α :=
  IsPullback.of_isLimit
    (PullbackCone.isLimitAux
      (PullbackCone.mk (map X α) (yoneda.map (projection X α)) (w X α))
      (lift X α) (by sorry) (by sorry) (by sorry))

end RestrictOverDiagonal

/-- The relative diagonal of the fibre presheaf is representable. -/
theorem restrictOver_representableDiagonal {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    yoneda.relativelyRepresentable (Limits.diag (restrictOverPresheaf X)) := by
  intro T α
  exact ⟨RestrictOverDiagonal.scheme X α, RestrictOverDiagonal.projection X α,
    RestrictOverDiagonal.map X α, RestrictOverDiagonal.isPullback X α⟩

namespace RestrictOverAtlasPullback

variable {S S' : Scheme.{u}} {g : S ⟶ S'} (X : Over (ofOver (Over.mk g)))
variable {T : Over S} (α : yoneda.obj T ⟶ restrictOverPresheaf X)

/-- The given fibre section considered as an original section over `S'`. -/
def sourceMap : yoneda.obj ((Over.map g).obj T) ⟶ X.left.functorOfPoints :=
  yonedaEquiv.symm (yonedaEquiv α).1

/-- The original atlas certificate supplies this actual pullback scheme. -/
def sourceScheme : Over S' :=
  (AtlasInput.representableEtale X.left).1.pullback (sourceMap X α)

def sourceProjection : sourceScheme X α ⟶ (Over.map g).obj T :=
  (AtlasInput.representableEtale X.left).1.snd (sourceMap X α)

def sourceAtlasProjection : sourceScheme X α ⟶ AtlasInput.scheme X.left :=
  (AtlasInput.representableEtale X.left).1.fst' (sourceMap X α)

def sourceIndex : sourceScheme X α ⟶ Over.mk g :=
  sourceProjection X α ≫ structureIndex g T

/-- The original pullback scheme with its induced map to `S`. -/
def scheme : Over S := Over.mk (sourceIndex X α).left

def projection : scheme X α ⟶ T :=
  Over.homMk (sourceProjection X α).left (by rfl)

/-- The original atlas projection commutes with the structure maps to `S`. -/
theorem atlasProjection_w :
    (sourceAtlasProjection X α).left ≫ (restrictOverAtlas X).hom =
      (scheme X α).hom := sorry

def atlasProjection : scheme X α ⟶ restrictOverAtlas X :=
  Over.homMk (sourceAtlasProjection X α).left (atlasProjection_w X α)

/-- The rebased atlas pullback has the original two scheme projections. -/
theorem w : yoneda.map (atlasProjection X α) ≫ restrictOverAtlasMap X =
    yoneda.map (projection X α) ≫ α := sorry

/-- A cone in the new base is a cone for the given original atlas pullback. -/
theorem sourceLift_condition {V : Over S} (a : V ⟶ restrictOverAtlas X) (f : V ⟶ T)
    (h : (restrictOverAtlasMap X).app (op V) a = α.app (op V) f) :
    (AtlasInput.map X.left).app (op ((Over.map g).obj V))
        ((Over.map g).map a ≫ (viewedIndexIso (restrictOverAtlasIndex X)).hom) =
      (sourceMap X α).app (op ((Over.map g).obj V)) ((Over.map g).map f) := sorry

/-- The lifted original arrow comes from the input atlas's actual pullback limit. -/
def sourceLift {V : Over S} (a : V ⟶ restrictOverAtlas X) (f : V ⟶ T)
    (h : (restrictOverAtlasMap X).app (op V) a = α.app (op V) f) :
    (Over.map g).obj V ⟶ sourceScheme X α :=
  (PullbackCone.IsLimit.equivPullbackObj
    (((AtlasInput.representableEtale X.left).1.isPullback (sourceMap X α)).app
      (op ((Over.map g).obj V))).isLimit).symm
    ⟨⟨(Over.map g).map a ≫ (viewedIndexIso (restrictOverAtlasIndex X)).hom,
      (Over.map g).map f⟩, sourceLift_condition X α a f h⟩

theorem liftPoint_mem {V : Over S} (a : V ⟶ restrictOverAtlas X) (f : V ⟶ T)
    (h : (restrictOverAtlasMap X).app (op V) a = α.app (op V) f) :
    (sourceLift X α a f h).left ≫ (scheme X α).hom = V.hom := sorry

/-- Its underlying scheme arrow is unchanged when regarded over `S`. -/
def liftPoint {V : Over S} (a : V ⟶ restrictOverAtlas X) (f : V ⟶ T)
    (h : (restrictOverAtlasMap X).app (op V) a = α.app (op V) f) :
    V ⟶ scheme X α :=
  Over.homMk (sourceLift X α a f h).left (liftPoint_mem X α a f h)

/-- Universal maps are the actual pointwise lifts of the given original pullback. -/
def lift (s : PullbackCone (restrictOverAtlasMap X) α) :
    s.pt ⟶ yoneda.obj (scheme X α) where
  app V := ofHom fun x ↦ liftPoint X α (s.fst.app V x) (s.snd.app V x)
    (ConcreteCategory.congr_hom (NatTrans.congr_app s.condition V) x)
  naturality := by sorry

/-- The representability certificate stores this explicit universal map. -/
theorem isPullback :
    IsPullback (yoneda.map (atlasProjection X α)) (yoneda.map (projection X α))
      (restrictOverAtlasMap X) α :=
  IsPullback.of_isLimit
    (PullbackCone.isLimitAux
      (PullbackCone.mk (yoneda.map (atlasProjection X α))
        (yoneda.map (projection X α)) (w X α))
      (lift X α) (by sorry) (by sorry) (by sorry))

/-- Étaleness is exactly the original supplied atlas's property on the same scheme arrow. -/
theorem projection_etale : (MorphismProperty.over (@Etale)) (projection X α) := by
  change Etale (sourceProjection X α).left
  exact (AtlasInput.representableEtale X.left).property_snd (sourceMap X α)

end RestrictOverAtlasPullback

/-- The original atlas map, viewed over `S`, is representable and étale. -/
theorem restrictOverAtlas_presheafEtale {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (MorphismProperty.over (@Etale)).presheaf (restrictOverAtlasMap X) := by
  letI : (MorphismProperty.over (@Etale) (X := S)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage (@Etale) (Over.forget S)
  apply MorphismProperty.relative.of_exists
  intro T α
  exact ⟨RestrictOverAtlasPullback.scheme X α,
    yoneda.map (RestrictOverAtlasPullback.atlasProjection X α),
    RestrictOverAtlasPullback.projection X α, RestrictOverAtlasPullback.isPullback X α,
    RestrictOverAtlasPullback.projection_etale X α⟩

/-- The explicit atlas image sieve is covering on every fibre section. -/
theorem restrictOverAtlas_imageSieve_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T : Over S} (s : restrictOverSection X T) :
    Presheaf.imageSieve (restrictOverAtlasMap X) s ∈ (Scheme.etaleTopology.over S) T := sorry

/-- The original covering atlas remains locally surjective after viewing it over `S`. -/
theorem restrictOverAtlas_locallySurjective {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (restrictOverAtlasMap X) where
  imageSieve_mem s := restrictOverAtlas_imageSieve_mem X s

/-- The fiber presheaf of an algebraic space over the representable base is an fppf sheaf
with representable diagonal and a representable étale locally-surjective atlas. -/
theorem restrictOver_spec {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (restrictOverPresheaf X) ∧
      yoneda.relativelyRepresentable (Limits.diag (restrictOverPresheaf X)) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ restrictOverPresheaf X),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨restrictOver_isSheaf X, restrictOver_representableDiagonal X,
    restrictOverAtlas X, restrictOverAtlasMap X,
    restrictOverAtlas_presheafEtale X, restrictOverAtlas_locallySurjective X⟩

/-- The algebraic space over `S` associated to a pair `(F', F' ⟶ S)` over `S'`. -/
def restrictOver {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) : AlgebraicSpace S :=
  ofFunctor (restrictOverPresheaf X) (restrictOver_spec X).1
    (restrictOver_spec X).2.1 (restrictOver_spec X).2.2

/-- The functor of points of `restrictOver X` is the fiber presheaf of `X.hom`. -/
@[simp]
theorem restrictOver_functorOfPoints {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (restrictOver X).functorOfPoints = restrictOverPresheaf X := sorry

/-- A morphism of pairs over `S` induces a map of fiber sections. -/
theorem restrictOverMap_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) {T : Over S}
    (s : restrictOverSection X T) :
    Y.hom.app (op ((Over.map g).obj T))
        (f.left.app (op ((Over.map g).obj T)) s.1) =
      structureIndex g T := sorry

/-- A morphism of pairs over `S'` induces a morphism of the associated spaces over `S`. -/
def restrictOverMap {S S' : Scheme.{u}} {g : S ⟶ S'}
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) :
    restrictOver X ⟶ restrictOver Y where
  app T := ofHom fun s ↦
    ⟨f.left.app (op ((Over.map g).obj T.unop)) s.1, restrictOverMap_mem f s⟩
  naturality := fun _ _ _ ↦ sorry

/-- The inverse comparison functor, sending a pair `(F', F' ⟶ S)` to its fiber over `S`. -/
def restrictOverFunctor {S S' : Scheme.{u}} (g : S ⟶ S') :
    Over (ofOver (Over.mk g)) ⥤ AlgebraicSpace S :=
  let laws : (∀ X : Over (ofOver (Over.mk g)),
      restrictOverMap (𝟙 X) = 𝟙 (restrictOver X)) ∧
      (∀ {X Y Z : Over (ofOver (Over.mk g))} (f : X ⟶ Y) (h : Y ⟶ Z),
        restrictOverMap (f ≫ h) = restrictOverMap f ≫ restrictOverMap h) := sorry
  { obj := fun X ↦ restrictOver X
    map := fun f ↦ restrictOverMap f
    map_id := laws.1
    map_comp := laws.2 }

/-- A section of `F` lies in the fiber of `extendBaseHom g F` over `structureIndex`. -/
theorem extendBaseUnitHom_app_mem {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S} (s : F.functorOfPoints.obj (op T)) :
    (extendBaseHom g F).app (op ((Over.map g).obj T))
        ⟨structureIndex g T,
          F.functorOfPoints.map (eqToHom (structureIndex_mk g T).symm).op s⟩ =
      structureIndex g T := sorry

/-- The component of the unit at an object of `Over S`. -/
def extendBaseUnitHom_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S} (s : F.functorOfPoints.obj (op T)) :
    restrictOverSection (Over.mk (extendBaseHom g F)) T :=
  ⟨⟨structureIndex g T,
      F.functorOfPoints.map (eqToHom (structureIndex_mk g T).symm).op s⟩,
    extendBaseUnitHom_app_mem g F s⟩

/-- The unit morphism `F ⟶ restrictOver (j_! F ⟶ S)`. -/
def extendBaseUnitHom {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    F ⟶ restrictOver (Over.mk (extendBaseHom g F)) where
  app T := ofHom fun s ↦ extendBaseUnitHom_app g F s
  naturality := fun _ _ _ ↦ sorry

/-- The index of a fiber of `extendBaseHom g F` over `structureIndex` recovers `T`. -/
theorem restrictOverSection_extendBase_mk {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S}
    (σ : restrictOverSection (Over.mk (extendBaseHom g F)) T) :
    Over.mk σ.1.1.left = T := sorry

/-- The inverse unit extracts the `F`-component of a fiber of `extendBaseHom`. -/
def extendBaseUnitInv_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) {T : Over S}
    (σ : restrictOverSection (Over.mk (extendBaseHom g F)) T) :
    F.functorOfPoints.obj (op T) :=
  F.functorOfPoints.map (eqToHom (restrictOverSection_extendBase_mk g σ).symm).op σ.1.2

/-- The inverse unit morphism `restrictOver (j_! F ⟶ S) ⟶ F`. -/
def extendBaseUnitInv {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    restrictOver (Over.mk (extendBaseHom g F)) ⟶ F where
  app T := ofHom fun σ ↦ extendBaseUnitInv_app g F σ
  naturality := fun _ _ _ ↦ sorry

/-- The unit isomorphism of the change-of-base equivalence, at an algebraic space over `S`. -/
def extendBaseUnitAppIso {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    F ≅ restrictOver ((extendBaseOver g).obj F) :=
  let laws : (extendBaseUnitHom g F ≫ extendBaseUnitInv g F = 𝟙 F) ∧
      (extendBaseUnitInv g F ≫ extendBaseUnitHom g F =
        𝟙 (restrictOver ((extendBaseOver g).obj F))) := sorry
  { hom := extendBaseUnitHom g F
    inv := extendBaseUnitInv g F
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- Naturality of the unit components. -/
theorem extendBaseUnitIso_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : AlgebraicSpace S} (f : F ⟶ G) :
    f ≫ (extendBaseUnitAppIso g G).hom =
      (extendBaseUnitAppIso g F).hom ≫
        (extendBaseOver g ⋙ restrictOverFunctor g).map f := sorry

/-- The unit isomorphism `𝟭 ≅ extendBaseOver g ⋙ restrictOverFunctor g`. -/
def extendBaseUnitIso {S S' : Scheme.{u}} (g : S ⟶ S') :
    𝟭 (AlgebraicSpace S) ≅ extendBaseOver g ⋙ restrictOverFunctor g :=
  let laws : (∀ {F G : AlgebraicSpace S} (f : F ⟶ G),
      (extendBaseOver g ⋙ restrictOverFunctor g).map f ≫ extendBaseUnitInv g G =
        extendBaseUnitInv g F ≫ f) ∧
      (∀ F : AlgebraicSpace S,
        extendBaseUnitHom g F ≫ extendBaseUnitInv g F = 𝟙 F) ∧
      (∀ F : AlgebraicSpace S,
        extendBaseUnitInv g F ≫ extendBaseUnitHom g F =
          𝟙 ((extendBaseOver g ⋙ restrictOverFunctor g).obj F)) := sorry
  { hom :=
      { app := fun F ↦ extendBaseUnitHom g F
        naturality := fun _ _ f ↦ extendBaseUnitIso_naturality g f }
    inv :=
      { app := fun F ↦ extendBaseUnitInv g F
        naturality := fun _ _ f ↦ laws.1 f }
    hom_inv_id := by
      apply NatTrans.ext
      funext F
      exact laws.2.1 F
    inv_hom_id := by
      apply NatTrans.ext
      funext F
      exact laws.2.2 F }

/-- Transporting a fiber section along `viewedIndexIso` yields a section of `X.left`. -/
def extendBaseCounitHom_app {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (σ : (extendBasePresheaf g (restrictOverPresheaf X)).obj (op T')) :
    X.left.functorOfPoints.obj (op T') :=
  X.left.functorOfPoints.map (viewedIndexIso σ.1).inv.op σ.2.1

/-- The forward counit map `j_! (restrictOver X) ⟶ X.left`. -/
def extendBaseCounitHom {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    extendBase g (restrictOver X) ⟶ X.left where
  app T' := ofHom fun σ ↦ extendBaseCounitHom_app X σ
  naturality := fun _ _ _ ↦ sorry

/-- A section of `X.left` over `T'` lies in the fiber over its structure map. -/
theorem extendBaseCounitInv_app_mem {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (t : X.left.functorOfPoints.obj (op T')) :
    X.hom.app (op ((Over.map g).obj (Over.mk (X.hom.app (op T') t).left)))
        (X.left.functorOfPoints.map (viewedIndexIso (X.hom.app (op T') t)).hom.op t) =
      structureIndex g (Over.mk (X.hom.app (op T') t).left) := sorry

/-- The inverse counit packages a section of `X.left` as a coproduct fiber. -/
def extendBaseCounitInv_app {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) {T' : Over S'}
    (t : X.left.functorOfPoints.obj (op T')) :
    (extendBasePresheaf g (restrictOverPresheaf X)).obj (op T') :=
  ⟨X.hom.app (op T') t,
    ⟨X.left.functorOfPoints.map (viewedIndexIso (X.hom.app (op T') t)).hom.op t,
      extendBaseCounitInv_app_mem X t⟩⟩

/-- The inverse counit map `X.left ⟶ j_! (restrictOver X)`. -/
def extendBaseCounitInv {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    X.left ⟶ extendBase g (restrictOver X) where
  app T' := ofHom fun t ↦ extendBaseCounitInv_app X t
  naturality := fun _ _ _ ↦ sorry

/-- The underlying isomorphism of algebraic spaces in the counit. -/
def extendBaseCounitLeftIso {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    extendBase g (restrictOver X) ≅ X.left :=
  let laws : (extendBaseCounitHom X ≫ extendBaseCounitInv X =
      𝟙 (extendBase g (restrictOver X))) ∧
      (extendBaseCounitInv X ≫ extendBaseCounitHom X = 𝟙 X.left) := sorry
  { hom := extendBaseCounitHom X
    inv := extendBaseCounitInv X
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The counit isomorphism of algebraic spaces commutes with the structure morphisms to `S`. -/
theorem extendBaseCounitLeftIso_w {S S' : Scheme.{u}} {g : S ⟶ S'}
    (X : Over (ofOver (Over.mk g))) :
    (extendBaseCounitLeftIso X).hom ≫ X.hom =
      ((restrictOverFunctor g ⋙ extendBaseOver g).obj X).hom := sorry

/-- The counit isomorphism at a pair `(F', F' ⟶ S)`. -/
def extendBaseCounitAppIso {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over (ofOver (Over.mk g))) :
    (restrictOverFunctor g ⋙ extendBaseOver g).obj X ≅ X :=
  let laws : (extendBaseCounitInv X ≫
      ((restrictOverFunctor g ⋙ extendBaseOver g).obj X).hom = X.hom) ∧
      (extendBaseCounitHom X ≫ extendBaseCounitInv X =
        𝟙 ((restrictOverFunctor g ⋙ extendBaseOver g).obj X).left) ∧
      (extendBaseCounitInv X ≫ extendBaseCounitHom X = 𝟙 X.left) := sorry
  { hom := Over.homMk (extendBaseCounitHom X) (extendBaseCounitLeftIso_w X)
    inv := Over.homMk (extendBaseCounitInv X) laws.1
    hom_inv_id := by
      apply Over.OverMorphism.ext
      exact laws.2.1
    inv_hom_id := by
      apply Over.OverMorphism.ext
      exact laws.2.2 }

/-- Naturality of the counit components. -/
theorem extendBaseCounitIso_naturality {S S' : Scheme.{u}} (g : S ⟶ S')
    {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y) :
    (restrictOverFunctor g ⋙ extendBaseOver g).map f ≫
        (extendBaseCounitAppIso g Y).hom =
      (extendBaseCounitAppIso g X).hom ≫ f := sorry

/-- The counit isomorphism `restrictOverFunctor g ⋙ extendBaseOver g ≅ 𝟭`. -/
def extendBaseCounitIso {S S' : Scheme.{u}} (g : S ⟶ S') :
    restrictOverFunctor g ⋙ extendBaseOver g ≅ 𝟭 (Over (ofOver (Over.mk g))) :=
  let laws : (∀ {X Y : Over (ofOver (Over.mk g))} (f : X ⟶ Y),
      f ≫ (extendBaseCounitAppIso g Y).inv =
        (extendBaseCounitAppIso g X).inv ≫
          (restrictOverFunctor g ⋙ extendBaseOver g).map f) ∧
      (∀ X : Over (ofOver (Over.mk g)),
        (extendBaseCounitAppIso g X).hom ≫ (extendBaseCounitAppIso g X).inv =
          𝟙 ((restrictOverFunctor g ⋙ extendBaseOver g).obj X)) ∧
      (∀ X : Over (ofOver (Over.mk g)),
        (extendBaseCounitAppIso g X).inv ≫ (extendBaseCounitAppIso g X).hom = 𝟙 X) := sorry
  { hom :=
      { app := fun X ↦ (extendBaseCounitAppIso g X).hom
        naturality := fun _ _ f ↦ extendBaseCounitIso_naturality g f }
    inv :=
      { app := fun X ↦ (extendBaseCounitAppIso g X).inv
        naturality := fun _ _ f ↦ laws.1 f }
    hom_inv_id := by
      apply NatTrans.ext
      funext X
      exact laws.2.1 X
    inv_hom_id := by
      apply NatTrans.ext
      funext X
      exact laws.2.2 X }

/-- Let `g : S ⟶ S'` be a morphism of the big fppf site. The assignment
sending an algebraic space `F` over `S` to the pair `(j_! F, j_! F ⟶ S)`, encoded as the
object `Over.mk (extendBaseHom g F)` of `Over (ofOver (Over.mk g))`, is an equivalence
between algebraic spaces over `S` and algebraic spaces `F'` over `S'` equipped with a
morphism `F' ⟶ S` of algebraic spaces over `S'`. -/
@[stacks 04SG]
def extendBaseEquivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    AlgebraicSpace S ≌ Over (ofOver (Over.mk g)) where
  functor := extendBaseOver g
  inverse := restrictOverFunctor g
  unitIso := extendBaseUnitIso g
  counitIso := extendBaseCounitIso g
  functor_unitIso_comp := by
    intro F
    sorry

/-- The forward functor of `extendBaseEquivalence g` is `extendBaseOver g`. -/
@[simp]
theorem extendBaseEquivalence_functor {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseEquivalence g).functor = extendBaseOver g := sorry

/-- The inverse functor of `extendBaseEquivalence g` is `restrictOverFunctor g`. -/
@[simp]
theorem extendBaseEquivalence_inverse {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseEquivalence g).inverse = restrictOverFunctor g := sorry

/-- On objects, the inverse of `extendBaseEquivalence g` is `restrictOver`. -/
@[simp]
theorem extendBaseEquivalence_inverse_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over (ofOver (Over.mk g))) :
    (extendBaseEquivalence g).inverse.obj X = restrictOver X := sorry

/-- `extendBaseOver g` is an equivalence of categories. -/
instance extendBaseOver_isEquivalence {S S' : Scheme.{u}} (g : S ⟶ S') :
    (extendBaseOver g).IsEquivalence :=
  (extendBaseEquivalence g).isEquivalence_functor

end AlgebraicGeometry.AlgebraicSpace
