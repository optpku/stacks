module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Extension of the base of algebraic spaces

For a morphism `g : S ⟶ S'`, extend a functor of points by taking the coproduct
over lifts of each test scheme's structure morphism through `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

private instance etaleOverIsMultiplicative {S : Scheme.{u}} :
    ((MorphismProperty.over (@Etale)) : MorphismProperty (Over S)).IsMultiplicative := by
  change (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) (Over.forget S)).IsMultiplicative
  infer_instance

private instance etaleOverRespectsIso {S : Scheme.{u}} :
    ((MorphismProperty.over (@Etale)) : MorphismProperty (Over S)).RespectsIso := by
  change (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) (Over.forget S)).RespectsIso
  infer_instance

/-- A morphism of schemes over `S'` induces a morphism over `S` after choosing
a lift of its target's structure morphism through `g : S ⟶ S'`. -/
def restrictIndex {S S' : Scheme.{u}} {T' T'' : Over S'} {g : S ⟶ S'}
    (f : T'' ⟶ T') (φ : T' ⟶ Over.mk g) :
    Over.mk (f ≫ φ).left ⟶ Over.mk φ.left :=
  Over.homMk f.left

/-- The first projection of `restrictIndex f φ` is `f`. -/
@[simp]
theorem restrictIndex_left {S S' : Scheme.{u}} {T' T'' : Over S'} {g : S ⟶ S'}
    (f : T'' ⟶ T') (φ : T' ⟶ Over.mk g) :
    (restrictIndex f φ).left = f.left := sorry

/-- Extension along `g : S ⟶ S'` sends a presheaf `F` to the presheaf whose
sections on `T'` are a lift `φ : T' ⟶ Over.mk g` and a section of `F` on
`T'` viewed over `S` through `φ`. -/
def extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S') (F : (Over S)ᵒᵖ ⥤ Type u) :
    (Over S')ᵒᵖ ⥤ Type u :=
  let obj := fun T' : (Over S')ᵒᵖ ↦
    Σ φ : T'.unop ⟶ Over.mk g, F.obj (op (Over.mk φ.left))
  let map : ∀ {T' T'' : (Over S')ᵒᵖ}, (T' ⟶ T'') → (obj T' ⟶ obj T'') :=
    fun f ↦ ofHom fun σ ↦
      ⟨f.unop ≫ σ.1, F.map (restrictIndex f.unop σ.1).op σ.2⟩
  let laws : (∀ T', map (𝟙 T') = 𝟙 (obj T')) ∧
      (∀ {T' T'' T''' : (Over S')ᵒᵖ} (f : T' ⟶ T'') (h : T'' ⟶ T'''),
        map (f ≫ h) = map f ≫ map h) := sorry
  { obj := obj, map := map, map_id := laws.1, map_comp := laws.2 }

/-- Evaluating `extendBasePresheaf g F` on `T'` is the coproduct of the values of `F` over
morphisms `T' ⟶ Over.mk g`. -/
theorem extendBasePresheaf_map_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) {T' T'' : Over S'} (f : T'' ⟶ T')
    (φ : T' ⟶ Over.mk g) (s : F.obj (op (Over.mk φ.left))) :
    (extendBasePresheaf g F).map f.op ⟨φ, s⟩ =
      ⟨f ≫ φ, F.map (restrictIndex f φ).op s⟩ := sorry

/-- A morphism of presheaves over `S` induces a morphism of their `j_!` coproduct
presheaves over `S'`. -/
def extendBasePresheafMap {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G) :
    extendBasePresheaf g F ⟶ extendBasePresheaf g G where
  app T' := ofHom fun σ ↦ ⟨σ.1, α.app (op (Over.mk σ.1.left)) σ.2⟩
  naturality := fun _ _ _ ↦ sorry

/-- Applying `extendBasePresheafMap` keeps the index and applies `α` on the corresponding
summand. -/
theorem extendBasePresheafMap_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} (α : F ⟶ G) {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (s : F.obj (op (Over.mk φ.left))) :
    (extendBasePresheafMap g α).app (op T') ⟨φ, s⟩ =
      ⟨φ, α.app (op (Over.mk φ.left)) s⟩ := sorry

/-- Assemble a morphism `T' ⟶ j(X)` from an index `φ : T' ⟶ S` over `S'` and a morphism
over `S` into `X`. -/
def homOfIndex {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    T' ⟶ (Over.map g).obj X :=
  Over.homMk β.left (by sorry)

/-- The underlying scheme morphism of `homOfIndex g φ β` is `β.left`. -/
@[simp]
theorem homOfIndex_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    (homOfIndex g φ β).left = β.left := sorry

/-- The index `T' ⟶ Over.mk g` associated to a morphism `T' ⟶ j(X)`. -/
def indexOfHom {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) : T' ⟶ Over.mk g :=
  Over.homMk (α.left ≫ X.hom) (by sorry)

/-- The underlying scheme morphism of `indexOfHom g α` is `α.left ≫ X.hom`. -/
@[simp]
theorem indexOfHom_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    (indexOfHom g α).left = α.left ≫ X.hom := sorry

/-- The morphism over `S` into `X` associated to a morphism `T' ⟶ j(X)`. -/
def homOverOfHom {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    Over.mk (indexOfHom g α).left ⟶ X :=
  Over.homMk α.left

/-- The underlying scheme morphism of `homOverOfHom g α` is `α.left`. -/
@[simp]
theorem homOverOfHom_left {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S} {T' : Over S'}
    (α : T' ⟶ (Over.map g).obj X) :
    (homOverOfHom g α).left = α.left := sorry

/-- The coproduct extension of a representable presheaf represents the same scheme
viewed over the new base. -/
def extendBasePresheafYonedaIso {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    extendBasePresheaf g (yoneda.obj X) ≅ yoneda.obj ((Over.map g).obj X) :=
  let forward : ∀ T' : (Over S')ᵒᵖ,
      (extendBasePresheaf g (yoneda.obj X)).obj T' →
        (yoneda.obj ((Over.map g).obj X)).obj T' :=
    fun T' element ↦ homOfIndex g element.1 element.2
  let inverse : ∀ T' : (Over S')ᵒᵖ,
      (yoneda.obj ((Over.map g).obj X)).obj T' →
        (extendBasePresheaf g (yoneda.obj X)).obj T' :=
    fun T' morphism ↦ ⟨indexOfHom g morphism, homOverOfHom g morphism⟩
  let laws : (∀ T', Function.LeftInverse (inverse T') (forward T')) ∧
      (∀ T', Function.RightInverse (inverse T') (forward T')) ∧
      (∀ {T' T'' : (Over S')ᵒᵖ} (morphism : T' ⟶ T''),
        (extendBasePresheaf g (yoneda.obj X)).map morphism ≫ ofHom (forward T'') =
          ofHom (forward T') ≫ (yoneda.obj ((Over.map g).obj X)).map morphism) := sorry
  NatIso.ofComponents (fun T' ↦ Equiv.toIso
    { toFun := forward T'
      invFun := inverse T'
      left_inv := laws.1 T'
      right_inv := laws.2.1 T' }) laws.2.2

/-- The forward map of `extendBasePresheafYonedaIso` packages an index and a slice morphism
into a morphism over `S'`. -/
theorem extendBasePresheafYonedaIso_hom_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over S) {T' : Over S'} (φ : T' ⟶ Over.mk g) (β : Over.mk φ.left ⟶ X) :
    (extendBasePresheafYonedaIso g X).hom.app (op T') ⟨φ, β⟩ = homOfIndex g φ β := sorry

/-- The inverse map of `extendBasePresheafYonedaIso` splits a morphism over `S'` into its
index and its morphism over `S`. -/
theorem extendBasePresheafYonedaIso_inv_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X : Over S) {T' : Over S'} (α : T' ⟶ (Over.map g).obj X) :
    (extendBasePresheafYonedaIso g X).inv.app (op T') α =
      ⟨indexOfHom g α, homOverOfHom g α⟩ := sorry

/-- The canonical unit sends a section to the summand indexed by its structure map
to the original base. -/
def extendBasePresheafUnit {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) : F ⟶ (Over.map g).op ⋙ extendBasePresheaf g F where
  app T := ofHom fun element ↦ ⟨Over.homMk T.unop.hom, element⟩
  naturality := by sorry

/-- The coproduct presheaf with its canonical unit is the left Kan extension along
the opposite of the change-of-base localization functor. -/
instance instIsLeftKanExtensionExtendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) :
    (extendBasePresheaf g F).IsLeftKanExtension (extendBasePresheafUnit g F) := sorry

/-- Extension along a morphism of base schemes preserves the fppf sheaf condition. -/
theorem isSheaf_extendBasePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') (extendBasePresheaf g F) := sorry

/-- A section of a supplied pullback square of types, using its actual limiting lift. -/
def pullbackPoint {P X Y Z : Type u} {l : P ⟶ X} {r : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback l r f g)
    (x : X) (y : Y) (w : f x = g y) : P :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨x, y⟩, w⟩

/-- Pointwise specified pullback sections give the actual natural limiting lift.
The supplied equalities and uniqueness are only the laws of that specified function. -/
theorem isPullback_of_pointLift {C : Type (u + 1)} [Category.{u} C]
    {P X Y Z : Cᵒᵖ ⥤ Type u} (l : P ⟶ X) (r : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (w : l ≫ f = r ≫ g)
    (lift : ∀ (V : Cᵒᵖ) (x : X.obj V) (y : Y.obj V), f.app V x = g.app V y → P.obj V)
    (fac_l : ∀ V x y h, l.app V (lift V x y h) = x)
    (fac_r : ∀ V x y h, r.app V (lift V x y h) = y)
    (uniq : ∀ V (z : P.obj V) x y h,
      l.app V z = x → r.app V z = y → z = lift V x y h) : IsPullback l r f g :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun c ↦
      { app := fun V ↦ ofHom fun z ↦
          lift V (c.fst.app V z) (c.snd.app V z) (congrArg (fun k ↦ k z) (NatTrans.congr_app c.condition V))
        naturality := by sorry })
    (by intro c; ext V z; exact fac_l _ _ _ _)
    (by intro c; ext V z; exact fac_r _ _ _ _)
    (by intro c m hm₁ hm₂; ext V z; exact uniq _ _ _ _ _ (by sorry) (by sorry)))

/-- The section of the original presheaf selected by the displayed summand of a test section. -/
private def extendBaseTestSection {S S' : Scheme.{u}} (g : S ⟶ S')
    {G : (Over S)ᵒᵖ ⥤ Type u} {T : Over S'}
    (α : yoneda.obj T ⟶ extendBasePresheaf g G) :
    yoneda.obj (Over.mk (yonedaEquiv α).1.left) ⟶ G :=
  yonedaEquiv.symm (yonedaEquiv α).2

/-- The representing scheme is the original supplied pullback, viewed over the new base. -/
private def extendBasePullback {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g G) : Over S' :=
  (Over.map g).obj (hη.pullback (extendBaseTestSection g α))

/-- The second projection retains the original pullback's underlying scheme map. -/
private def extendBasePullbackSnd {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g G) :
    extendBasePullback g hη α ⟶ T :=
  Over.homMk (hη.snd (extendBaseTestSection g α)).left (by sorry)

/-- The first projection is the original represented projection and the actual Yoneda comparison. -/
private def extendBasePullbackFst {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g G) :
    yoneda.obj (extendBasePullback g hη α) ⟶ extendBasePresheaf g F :=
  (extendBasePresheafYonedaIso g (hη.pullback (extendBaseTestSection g α))).inv ≫
    extendBasePresheafMap g (hη.fst (extendBaseTestSection g α))

/-- Equality of extended sections identifies their actual structure-map indices. -/
private theorem extendBasePullback_index {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G} {T V : Over S'}
    (α : yoneda.obj T ⟶ extendBasePresheaf g G)
    (x : (extendBasePresheaf g F).obj (op V)) (y : V ⟶ T)
    (h : (extendBasePresheafMap g η).app (op V) x = α.app (op V) y) :
    x.1 = y ≫ (yonedaEquiv α).1 := sorry

/-- The new section lift uses the original represented pullback's actual lift after
transporting its section along the equality of the displayed structure-map indices. -/
private def extendBasePullbackLift {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T V : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g G)
    (x : (extendBasePresheaf g F).obj (op V)) (y : V ⟶ T)
    (h : (extendBasePresheafMap g η).app (op V) x = α.app (op V) y) :
    V ⟶ extendBasePullback g hη α := by
  let φ := (yonedaEquiv α).1
  let β := extendBaseTestSection g α
  let V₀ : Over S := Over.mk (y ≫ φ).left
  let x₀ : F.obj (op V₀) := Eq.mp
    (congrArg (fun ψ : V ⟶ Over.mk g ↦ F.obj (op (Over.mk ψ.left)))
      (extendBasePullback_index g α x y h)) x.2
  let y₀ : V₀ ⟶ Over.mk φ.left := restrictIndex y φ
  let z := pullbackPoint ((hη.isPullback β).app (op V₀)) x₀ y₀ (by sorry)
  exact homOfIndex g (y ≫ φ) z

/-- Extension preserves a scheme-morphism property by retaining the original
representing scheme and its identical underlying second projection. -/
theorem extendBasePresheafMap_etale {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S)ᵒᵖ ⥤ Type u} {η : F ⟶ G}
    (hη : (MorphismProperty.over (@Etale)).presheaf η) :
    (MorphismProperty.over (@Etale)).presheaf (extendBasePresheafMap g η) := by
  apply MorphismProperty.relative.of_exists
  intro T α
  let h := hη.rep
  refine ⟨extendBasePullback g h α, extendBasePullbackFst g h α,
    extendBasePullbackSnd g h α, ?_, ?_⟩
  · exact isPullback_of_pointLift _ _ _ _ (by sorry)
      (fun V x y hxy ↦ extendBasePullbackLift g h α x y hxy)
      (by sorry) (by sorry) (by sorry)
  · exact hη.property_snd (extendBaseTestSection g α)

/-- The original atlas scheme is viewed over the new base. -/
private def extendBaseAtlas {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    Over S' :=
  (Over.map g).obj F.atlas.choose

/-- The new atlas map is the actual extension of the given original atlas. -/
private def extendBaseAtlasMap {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    yoneda.obj (extendBaseAtlas g F) ⟶ extendBasePresheaf g F.functorOfPoints :=
  (extendBasePresheafYonedaIso g F.atlas.choose).inv ≫
    extendBasePresheafMap g F.atlas.choose_spec.choose

/-- Extending a represented étale map `h_X ⟶ G` and transporting along `h_{j(X)} ≅ j_! h_X`
retains the original represented pullbacks and étale projections. -/
theorem extendBasePresheafYonedaMap_etale {S S' : Scheme.{u}} (g : S ⟶ S') {X : Over S}
    {G : (Over S)ᵒᵖ ⥤ Type u} {η : yoneda.obj X ⟶ G}
    (hη : (MorphismProperty.over (@Etale)).presheaf η) :
    (MorphismProperty.over (@Etale)).presheaf
      ((extendBasePresheafYonedaIso g X).inv ≫ extendBasePresheafMap g η) := by
  exact ((MorphismProperty.over (@Etale)).presheaf).comp_mem _ _
    (((MorphismProperty.over (@Etale)).presheaf).of_isIso _)
    (extendBasePresheafMap_etale g hη)

/-- The atlas representation and its étale scheme projections retain actual original factors. -/
private theorem extendBaseAtlas_etale {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    (MorphismProperty.over (@Etale)).presheaf (extendBaseAtlasMap g F) :=
  extendBasePresheafYonedaMap_etale g F.atlas.choose_spec.choose_spec.1

/-- Original local atlas lifts remain local atlas lifts in their specified structure-map summands. -/
private theorem extendBaseAtlas_locallySurjective {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S') (extendBaseAtlasMap g F) := sorry

/-- The first extended section supplied by an arbitrary test pair. -/
private def extendBaseDiagonalFirst {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :=
  yonedaEquiv (α ≫ prod.fst)

/-- The second extended section supplied by the same arbitrary test pair. -/
private def extendBaseDiagonalSecond {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :=
  yonedaEquiv (α ≫ prod.snd)

/-- The actual equality scheme of the two possibly different lifts to the original base. -/
private def extendBaseDiagonalEqualizer {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) : Over S :=
  Over.mk (equalizer.ι (extendBaseDiagonalFirst g F α).1.left
    (extendBaseDiagonalSecond g F α).1.left ≫ (extendBaseDiagonalFirst g F α).1.left)

/-- The equality scheme restricts the first original section. -/
private def extendBaseDiagonalFirstMap {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :
    extendBaseDiagonalEqualizer g F α ⟶ Over.mk (extendBaseDiagonalFirst g F α).1.left :=
  Over.homMk (equalizer.ι _ _) rfl

/-- The equalizer condition gives the same actual structure map for the second section. -/
private def extendBaseDiagonalSecondMap {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :
    extendBaseDiagonalEqualizer g F α ⟶ Over.mk (extendBaseDiagonalSecond g F α).1.left :=
  Over.homMk (equalizer.ι _ _) (equalizer.condition _ _).symm

/-- The two original sections now have the same base, so the supplied original diagonal represents them. -/
private def extendBaseDiagonalPair {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :
    yoneda.obj (extendBaseDiagonalEqualizer g F α) ⟶ F.functorOfPoints ⨯ F.functorOfPoints :=
  prod.lift
    (yonedaEquiv.symm (F.functorOfPoints.map (extendBaseDiagonalFirstMap g F α).op
      (extendBaseDiagonalFirst g F α).2))
    (yonedaEquiv.symm (F.functorOfPoints.map (extendBaseDiagonalSecondMap g F α).op
      (extendBaseDiagonalSecond g F α).2))

/-- The actual original coincidence scheme, viewed over the new base. -/
private def extendBaseDiagonalPullback {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) : Over S' :=
  (Over.map g).obj (F.representableDiagonal.pullback (extendBaseDiagonalPair g F α))

/-- Compose the original diagonal projection with the actual base-lift equalizer inclusion. -/
private def extendBaseDiagonalSnd {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) : extendBaseDiagonalPullback g F α ⟶ T :=
  Over.homMk ((F.representableDiagonal.snd (extendBaseDiagonalPair g F α)).left ≫
    equalizer.ι (extendBaseDiagonalFirst g F α).1.left (extendBaseDiagonalSecond g F α).1.left)
    (by sorry)

/-- Extend the given diagonal model's original first projection. -/
private def extendBaseDiagonalFst {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints) :
    yoneda.obj (extendBaseDiagonalPullback g F α) ⟶ extendBasePresheaf g F.functorOfPoints :=
  (extendBasePresheafYonedaIso g
    (F.representableDiagonal.pullback (extendBaseDiagonalPair g F α))).inv ≫
      extendBasePresheafMap g (F.representableDiagonal.fst (extendBaseDiagonalPair g F α))

/-- The diagonal lift first factors the test map through the native equality scheme,
then uses the given original diagonal's actual represented pullback lift. -/
private def extendBaseDiagonalLift {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S)
    {T V : Over S'} (α : yoneda.obj T ⟶ extendBasePresheaf g F.functorOfPoints ⨯
      extendBasePresheaf g F.functorOfPoints)
    (x : (extendBasePresheaf g F.functorOfPoints).obj (op V)) (y : V ⟶ T)
    (h : (Limits.diag (extendBasePresheaf g F.functorOfPoints)).app (op V) x = α.app (op V) y) :
    V ⟶ extendBaseDiagonalPullback g F α := by
  let V₀ : Over S := Over.mk x.1.left
  let e := equalizer.lift y.left (by sorry : y.left ≫ (extendBaseDiagonalFirst g F α).1.left =
    y.left ≫ (extendBaseDiagonalSecond g F α).1.left)
  let e₀ : V₀ ⟶ extendBaseDiagonalEqualizer g F α := Over.homMk e (by sorry)
  let z := pullbackPoint ((F.representableDiagonal.isPullback
    (extendBaseDiagonalPair g F α)).app (op V₀)) x.2 e₀ (by sorry)
  exact homOfIndex g x.1 z

/-- The extended diagonal is represented by the actual original coincidence scheme
on the actual equality locus of the two structure-map lifts. -/
private theorem extendBase_representableDiagonal {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) :
    yoneda.relativelyRepresentable (Limits.diag (extendBasePresheaf g F.functorOfPoints)) := by
  intro T α
  refine ⟨extendBaseDiagonalPullback g F α, extendBaseDiagonalSnd g F α,
    extendBaseDiagonalFst g F α, ?_⟩
  exact isPullback_of_pointLift _ _ _ _ (by sorry)
    (fun V x y h ↦ extendBaseDiagonalLift g F α x y h)
    (by sorry) (by sorry) (by sorry)

/-- Coproduct extension of the functor of points of an algebraic space is an fppf sheaf
with representable diagonal and a representable étale locally-surjective atlas. -/
theorem extendBase_spec {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') (extendBasePresheaf g F.functorOfPoints) ∧
      yoneda.relativelyRepresentable (Limits.diag (extendBasePresheaf g F.functorOfPoints)) ∧
        ∃ (U : Over S') (p : yoneda.obj U ⟶ (extendBasePresheaf g F.functorOfPoints)),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S') p := by
  exact ⟨isSheaf_extendBasePresheaf g F.functorOfPoints F.isSheaf,
    extendBase_representableDiagonal g F, extendBaseAtlas g F, extendBaseAtlasMap g F,
    extendBaseAtlas_etale g F, extendBaseAtlas_locallySurjective g F⟩

/-- View an algebraic space over `S` as an algebraic space over `S'` along
`g : S ⟶ S'`, using the coproduct extension of its functor of points. -/
def extendBase {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    AlgebraicSpace S' :=
  ofFunctor (extendBasePresheaf g F.functorOfPoints) (extendBase_spec g F).1
    (extendBase_spec g F).2.1 (extendBase_spec g F).2.2

/-- The functor of points of `extendBase g F` is the coproduct presheaf `extendBasePresheaf`. -/
@[simp]
theorem extendBase_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S) :
    (extendBase g F).functorOfPoints = extendBasePresheaf g F.functorOfPoints := sorry

/-- Sections of the extended presheaf are the coproduct over lifts of the structure map. -/
theorem extendBasePresheaf_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) (T' : Over S') :
    (extendBasePresheaf g F).obj (op T') =
      Σ φ : T' ⟶ Over.mk g, F.obj (op (Over.mk φ.left)) := sorry

/-- Restriction of presheaves along `j = Over.map g` is precomposition with `(Over.map g).op`. -/
abbrev baseChangePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) : (Over S)ᵒᵖ ⥤ Type u :=
  (Over.map g).op ⋙ F'

/-- Evaluating `baseChangePresheaf g F'` on a morphism over `S` is evaluation of `F'` after
applying `Over.map g`. -/
theorem baseChangePresheaf_app {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) {T T' : Over S} (f : T ⟶ T') :
    (baseChangePresheaf g F').map f.op = F'.map ((Over.map g).map f).op := sorry

/-- The inverse image of a representable presheaf along `j = Over.map g` is the representable
presheaf of the chosen pullback `S ×_{S'} X'`. -/
def baseChangePresheafYonedaIso {S S' : Scheme.{u}} (g : S ⟶ S') (X' : Over S') :
    baseChangePresheaf g (yoneda.obj X') ≅ yoneda.obj ((Over.pullback g).obj X') :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso ((Over.mapPullbackAdj g).homEquiv T.unop X')) sorry

/-- The forward map of `baseChangePresheafYonedaIso` is the adjunction equivalence
`Over.map g ⊣ Over.pullback g`. -/
theorem baseChangePresheafYonedaIso_hom_apply {S S' : Scheme.{u}} (g : S ⟶ S')
    (X' : Over S') {T : Over S} (α : (Over.map g).obj T ⟶ X') :
    (baseChangePresheafYonedaIso g X').hom.app (op T) α =
      (Over.mapPullbackAdj g).homEquiv T X' α := sorry

/-- If `F'` is an fppf sheaf on `Over S'`, then `baseChangePresheaf g F'` is an fppf sheaf on
`Over S`. -/
theorem isSheaf_baseChangePresheaf {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u)
    (hF' : Presheaf.IsSheaf (Scheme.fppfTopology.over S') F') :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (baseChangePresheaf g F') := sorry

/-- A restricted test section is an original section on the same scheme viewed over the old base. -/
private def baseChangeTestSection {S S' : Scheme.{u}} (g : S ⟶ S')
    {G : (Over S')ᵒᵖ ⥤ Type u} {T : Over S}
    (α : yoneda.obj T ⟶ baseChangePresheaf g G) :
    yoneda.obj ((Over.map g).obj T) ⟶ G :=
  let testSection : (baseChangePresheaf g G).obj (op T) := yonedaEquiv α
  yonedaEquiv.symm testSection

/-- Rebase the original representing scheme using its actual projection to the given test scheme. -/
private def baseChangePullback {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g G) : Over S :=
  Over.mk ((hη.snd (baseChangeTestSection g α)).left ≫ T.hom)

/-- Viewing the rebased representing scheme over the old base recovers the original model. -/
private def baseChangePullbackViewedIso {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g G) :
    (Over.map g).obj (baseChangePullback g hη α) ≅ hη.pullback (baseChangeTestSection g α) :=
  Over.isoMk (Iso.refl _) (by sorry)

/-- The rebased second projection has exactly the original representing scheme morphism. -/
private def baseChangePullbackSnd {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g G) :
    baseChangePullback g hη α ⟶ T :=
  Over.homMk (hη.snd (baseChangeTestSection g α)).left rfl

/-- The first projection evaluates the original represented projection on the actual rebasing isomorphism. -/
private def baseChangePullbackFst {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g G) :
    yoneda.obj (baseChangePullback g hη α) ⟶ baseChangePresheaf g F :=
  yonedaEquiv.symm ((hη.fst (baseChangeTestSection g α)).app _
    (baseChangePullbackViewedIso g hη α).hom)

/-- The restricted represented pullback has the original universal section lift,
with its underlying scheme map rebased by the supplied cone projection. -/
private def baseChangePullbackLift {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G} (hη : yoneda.relativelyRepresentable η)
    {T V : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g G)
    (x : (baseChangePresheaf g F).obj (op V)) (y : V ⟶ T)
    (h : (Functor.whiskerLeft (Over.map g).op η).app (op V) x = α.app (op V) y) :
    V ⟶ baseChangePullback g hη α := by
  let β := baseChangeTestSection g α
  let z := pullbackPoint ((hη.isPullback β).app (op ((Over.map g).obj V)))
    x ((Over.map g).map y) (by sorry)
  exact Over.homMk z.left (by sorry)

/-- Restriction retains the original étale projection on the actual representing scheme. -/
theorem baseChangePresheafMap_etale {S S' : Scheme.{u}} (g : S ⟶ S')
    {F G : (Over S')ᵒᵖ ⥤ Type u} {η : F ⟶ G}
    (hη : (MorphismProperty.over (@Etale)).presheaf η) :
    (MorphismProperty.over (@Etale)).presheaf (Functor.whiskerLeft (Over.map g).op η) := by
  apply MorphismProperty.relative.of_exists
  intro T α
  let h := hη.rep
  refine ⟨baseChangePullback g h α, baseChangePullbackFst g h α,
    baseChangePullbackSnd g h α, ?_, ?_⟩
  · exact isPullback_of_pointLift _ _ _ _ (by sorry)
      (fun V x y h ↦ baseChangePullbackLift g hη.rep α x y h)
      (by sorry) (by sorry) (by sorry)
  · exact hη.property_snd (baseChangeTestSection g α)

/-- The new atlas scheme is the actual native scheme pullback of the original atlas. -/
private def baseChangeAtlas {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S') : Over S :=
  (Over.pullback g).obj F.atlas.choose

/-- The actual restricted original atlas map, with the native representable-domain comparison. -/
private def baseChangeAtlasMap {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S') :
    yoneda.obj (baseChangeAtlas g F) ⟶ baseChangePresheaf g F.functorOfPoints :=
  (baseChangePresheafYonedaIso g F.atlas.choose).inv ≫
    Functor.whiskerLeft (Over.map g).op F.atlas.choose_spec.choose

/-- Restricting a represented étale map `h_{X'} ⟶ G` and transporting along
`j^{-1} h_{X'} ≅ h_{X'_S}` retains the original represented pullbacks and étale projections. -/
theorem baseChangePresheafYonedaMap_etale {S S' : Scheme.{u}} (g : S ⟶ S') {X' : Over S'}
    {G : (Over S')ᵒᵖ ⥤ Type u} {η : yoneda.obj X' ⟶ G}
    (hη : (MorphismProperty.over (@Etale)).presheaf η) :
    (MorphismProperty.over (@Etale)).presheaf
      ((baseChangePresheafYonedaIso g X').inv ≫ Functor.whiskerLeft (Over.map g).op η) := by
  exact ((MorphismProperty.over (@Etale)).presheaf).comp_mem _ _
    (((MorphismProperty.over (@Etale)).presheaf).of_isIso _)
    (baseChangePresheafMap_etale g hη)

/-- Original represented étale atlas projections survive restriction and its explicit domain isomorphism. -/
private theorem baseChangeAtlas_etale {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S') :
    (MorphismProperty.over (@Etale)).presheaf (baseChangeAtlasMap g F) :=
  baseChangePresheafYonedaMap_etale g F.atlas.choose_spec.choose_spec.1

/-- Pulling the original local atlas lifts back gives local lifts of the specified atlas map. -/
private theorem baseChangeAtlas_locallySurjective {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S') :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (baseChangeAtlasMap g F) := sorry

/-- The original pair of sections on the test scheme viewed over the old base. -/
private def baseChangeDiagonalPair {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S')
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g F.functorOfPoints ⨯
      baseChangePresheaf g F.functorOfPoints) :
    yoneda.obj ((Over.map g).obj T) ⟶ F.functorOfPoints ⨯ F.functorOfPoints := by
  let x : (baseChangePresheaf g F.functorOfPoints).obj (op T) := yonedaEquiv (α ≫ prod.fst)
  let y : (baseChangePresheaf g F.functorOfPoints).obj (op T) := yonedaEquiv (α ≫ prod.snd)
  exact prod.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y)

/-- The restricted pair uses its actual product section, with no chosen product-comparison witness. -/
private def baseChangeDiagonalTest {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S')
    {T : Over S} (α : yoneda.obj T ⟶ baseChangePresheaf g F.functorOfPoints ⨯
      baseChangePresheaf g F.functorOfPoints) :
    yoneda.obj T ⟶ baseChangePresheaf g (F.functorOfPoints ⨯ F.functorOfPoints) := by
  let x : (F.functorOfPoints ⨯ F.functorOfPoints).obj (op ((Over.map g).obj T)) :=
    yonedaEquiv (baseChangeDiagonalPair g F α)
  exact yonedaEquiv.symm x

/-- The restricted diagonal has the actual rebased original diagonal model and its supplied limit lift. -/
private theorem baseChange_representableDiagonal {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : AlgebraicSpace S') :
    yoneda.relativelyRepresentable (Limits.diag (baseChangePresheaf g F.functorOfPoints)) := by
  intro T α
  let β := baseChangeDiagonalTest g F α
  let h := F.representableDiagonal
  refine ⟨baseChangePullback g h β, baseChangePullbackSnd g h β,
    baseChangePullbackFst g h β, ?_⟩
  exact isPullback_of_pointLift _ _ _ _ (by sorry)
    (fun V x y hxy ↦ baseChangePullbackLift g h β x y (by sorry))
    (by sorry) (by sorry) (by sorry)

/-- Restriction of the functor of points of an algebraic space is an fppf sheaf
with representable diagonal and a representable étale locally-surjective atlas. -/
theorem baseChange_spec {S S' : Scheme.{u}} (g : S ⟶ S') (F' : AlgebraicSpace S') :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (baseChangePresheaf g F'.functorOfPoints) ∧
      yoneda.relativelyRepresentable (Limits.diag (baseChangePresheaf g F'.functorOfPoints)) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (baseChangePresheaf g F'.functorOfPoints)),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  exact ⟨isSheaf_baseChangePresheaf g F'.functorOfPoints F'.isSheaf,
    baseChange_representableDiagonal g F', baseChangeAtlas g F', baseChangeAtlasMap g F',
    baseChangeAtlas_etale g F', baseChangeAtlas_locallySurjective g F'⟩

/-- Pull an algebraic space back along a base-scheme morphism by restricting its
functor of points. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') (F' : AlgebraicSpace S') :
    AlgebraicSpace S :=
  ofFunctor (baseChangePresheaf g F'.functorOfPoints) (baseChange_spec g F').1
    (baseChange_spec g F').2.1 (baseChange_spec g F').2.2

/-- The functor of points of `baseChange g F'` is restriction of the functor of points of
`F'` along `Over.map g`. -/
@[simp]
theorem baseChange_functorOfPoints {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : AlgebraicSpace S') :
    (baseChange g F').functorOfPoints = baseChangePresheaf g F'.functorOfPoints := sorry

/-- Restriction evaluates a presheaf on the test scheme viewed over the original base. -/
theorem baseChangePresheaf_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) (T : Over S) :
    (baseChangePresheaf g F').obj (op T) = F'.obj (op ((Over.map g).obj T)) := sorry

/-- The inverse image of a sheaf along `j = Over.map g` evaluates by applying `Over.map g` to
the slice object. -/
theorem overMapPullback_obj_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : Sheaf (Scheme.fppfTopology.over S') (Type u)) (T : Over S) :
    ((Scheme.fppfTopology.overMapPullback (Type u) g).obj F').obj.obj (op T) =
      F'.obj.obj (op ((Over.map g).obj T)) := sorry

end AlgebraicGeometry.AlgebraicSpace
