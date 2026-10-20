module

public import ReasLib.AlgebraicGeometry.AdditiveGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal

/-! The additive group over an algebraic space and its scheme-valued points. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AdditiveGroup

section

-- Local declaration justification (metaprogramming implementation): Exposed constructors retain private recognition and naturality proofs under Lean's module visibility rules.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The product with the additive group scheme satisfies fppf descent. -/
private theorem totalSpace_isSheaf {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X) := sorry

/-- The product with the additive group scheme has representable diagonal. -/
private theorem totalSpace_representableDiagonal {S : Scheme.{u}} (B : AlgebraicSpace S) :
    yoneda.relativelyRepresentable (Limits.diag
      (B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro U x
  let F := B.functorOfPoints
  let G := yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X
  let H := ⊤_ ((Over S)ᵒᵖ ⥤ Type u)
  let terminalDiagonalIso : H ≅ H ⨯ H :=
    { hom := Limits.diag H
      inv := prod.fst
      hom_inv_id := prod.lift_fst (𝟙 H) (𝟙 H)
      inv_hom_id := by
        apply prod.hom_ext
        · exact terminalIsTerminal.hom_ext _ _
        · exact terminalIsTerminal.hom_ext _ _ }
  let e := prodIsoPullback F G
  have hx := Functor.relativelyRepresentable.PullbackDiagonal.sectionRepresentable
    (terminal.from F) (terminal.from G) B.representableDiagonal
    (ofOver_representableDiagonal (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)
    (@Functor.relativelyRepresentable.of_isIso _ _ _ _ yoneda _ _
      terminalDiagonalIso.hom terminalDiagonalIso.isIso_hom) (x ≫ e.hom)
  have hx' := (yoneda.relativelyRepresentable).comp_mem _ _ hx
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
  simpa only [F, G, Category.assoc, e.hom_inv_id, Category.comp_id] using hx'

/-- The product with the additive group scheme admits a representable étale atlas. -/
private theorem totalSpace_hasAtlas {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ∃ (U : Over S) (atlasMap : yoneda.obj U ⟶
        B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) atlasMap ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) atlasMap := by
  let U := B.atlas.choose
  let atlasMap := B.atlas.choose_spec.choose
  let V := (AlgebraicGeometry.AdditiveGroup.groupScheme S).X
  let p : yoneda.obj (U ⨯ V) ⟶ B.functorOfPoints ⨯ yoneda.obj V :=
    prodComparison yoneda U V ≫ prod.map atlasMap (𝟙 (yoneda.obj V))
  refine ⟨U ⨯ V, p, ?_, ?_⟩
  · exact ⟨Functor.relativelyRepresentable.of_diag (totalSpace_representableDiagonal B) p,
      by sorry⟩
  · sorry

/-- The product of an algebraic space with the additive group scheme over its base. -/
def totalSpace {S : Scheme.{u}} (B : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)
    (totalSpace_isSheaf B) (totalSpace_representableDiagonal B) (totalSpace_hasAtlas B)

/-- The additive group space over `B`, with the first projection as structure morphism. -/
def groupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) : Over B :=
  Over.mk (Y := totalSpace B)
    (prod.fst : B.functorOfPoints ⨯
      yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X ⟶ B.functorOfPoints)

/-- The second projection from the additive group space to the additive group scheme. -/
def toGroupScheme {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace B).left ⟶ ofOver (AlgebraicGeometry.AdditiveGroup.groupScheme S).X :=
  (prod.snd : B.functorOfPoints ⨯
    yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X ⟶
      yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)

/-- The additive group space has product functor of points and first-projection structure map. -/
theorem groupSpace_spec {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace B).left.functorOfPoints =
        (B.functorOfPoints ⨯ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X) ∧
      (groupSpace B).hom =
        (prod.fst : B.functorOfPoints ⨯
          yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X ⟶ B.functorOfPoints) := sorry

/-- Zero sections commute with pullback along morphisms of test schemes. -/
private theorem zeroHom_naturality {S : Scheme.{u}} (E : AlgebraicSpace S)
    {T T' : (Over S)ᵒᵖ} (testMap : T ⟶ T') :
    E.functorOfPoints.map testMap ≫
        (↾fun (_ : E.functorOfPoints.obj T') ↦
          AlgebraicGeometry.AdditiveGroup.homOfSection S T'.unop 1) =
      (↾fun (_ : E.functorOfPoints.obj T) ↦
        AlgebraicGeometry.AdditiveGroup.homOfSection S T.unop 1) ≫
          (yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X).map testMap := sorry

/-- The zero point of the additive group scheme at every point of an algebraic space. -/
private def zeroHom {S : Scheme.{u}} (E : AlgebraicSpace S) :
    E ⟶ ofOver (AlgebraicGeometry.AdditiveGroup.groupScheme S).X where
  app T := ↾fun _ ↦ AlgebraicGeometry.AdditiveGroup.homOfSection S T.unop 1
  naturality := fun _ _ testMap ↦ zeroHom_naturality E testMap

/-- The zero section of the additive group space over `B`. -/
def one {S : Scheme.{u}} (B : AlgebraicSpace S) : B ⟶ (groupSpace B).left :=
  prod.lift (𝟙 B.functorOfPoints)
    (zeroHom B : B.functorOfPoints ⟶ yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)

/-- The zero section preserves the map to `B`. -/
theorem one_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    one B ≫ (groupSpace B).hom = 𝟙 B := sorry

/-- Pointwise addition of additive-group coordinates commutes with test-scheme pullback. -/
private theorem addHom_naturality {S : Scheme.{u}} {E : AlgebraicSpace S}
    (first second : E ⟶ ofOver (AlgebraicGeometry.AdditiveGroup.groupScheme S).X)
    {T T' : (Over S)ᵒᵖ} (testMap : T ⟶ T') :
    E.functorOfPoints.map testMap ≫
        (↾fun point ↦ (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T'.unop).symm
          (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T'.unop (first.app T' point) *
            AlgebraicGeometry.AdditiveGroup.homMulEquiv S T'.unop (second.app T' point))) =
      (↾fun point ↦ (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop).symm
        (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop (first.app T point) *
          AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop (second.app T point))) ≫
            (yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X).map testMap := sorry

/-- Pointwise addition of two morphisms to the additive group scheme. -/
def addHom {S : Scheme.{u}} {E : AlgebraicSpace S}
    (first second : E ⟶ ofOver (AlgebraicGeometry.AdditiveGroup.groupScheme S).X) :
    E ⟶ ofOver (AlgebraicGeometry.AdditiveGroup.groupScheme S).X where
  app T := ↾fun point ↦ (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop).symm
    (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop (first.app T point) *
      AlgebraicGeometry.AdditiveGroup.homMulEquiv S T.unop (second.app T point))
  naturality := fun _ _ testMap ↦ addHom_naturality first second testMap

end

/-- Addition on the additive group space, retaining the common coordinate in `B`. -/
def mul {S : Scheme.{u}} (B : AlgebraicSpace S) :
    pullback (groupSpace B).hom (groupSpace B).hom ⟶ (groupSpace B).left :=
  prod.lift
    ((pullback.fst (groupSpace B).hom (groupSpace B).hom ≫ (groupSpace B).hom) :
      (pullback (groupSpace B).hom (groupSpace B).hom).functorOfPoints ⟶ B.functorOfPoints)
    (addHom (pullback.fst (groupSpace B).hom (groupSpace B).hom ≫ toGroupScheme B)
      (pullback.snd (groupSpace B).hom (groupSpace B).hom ≫ toGroupScheme B))

/-- Addition preserves the common coordinate in `B`. -/
theorem mul_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    mul B ≫ (groupSpace B).hom =
      pullback.fst (groupSpace B).hom (groupSpace B).hom ≫ (groupSpace B).hom := sorry

/-- Negation on the additive group space, retaining the coordinate in `B`. -/
def inv {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace B).left ⟶ (groupSpace B).left :=
  prod.lift (C := (Over S)ᵒᵖ ⥤ Type u)
    ((groupSpace B).hom : (groupSpace B).left.functorOfPoints ⟶ B.functorOfPoints)
    ((toGroupScheme B : (groupSpace B).left.functorOfPoints ⟶
      yoneda.obj (AlgebraicGeometry.AdditiveGroup.groupScheme S).X) ≫
        yoneda.map (ι[(AlgebraicGeometry.AdditiveGroup.groupScheme S).X]))

/-- Negation preserves the coordinate in `B`. -/
theorem inv_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    inv B ≫ (groupSpace B).hom = (groupSpace B).hom := sorry

/-- The zero section as a morphism in the slice category. -/
def oneHom {S : Scheme.{u}} (B : AlgebraicSpace S) :
    𝟙_ (Over B) ⟶ groupSpace B :=
  Over.homMk (one B) (one_w B)

/-- Addition as a morphism in the slice category. -/
def mulMap {S : Scheme.{u}} (B : AlgebraicSpace S) :
    groupSpace B ⊗ groupSpace B ⟶ groupSpace B :=
  Over.homMk (mul B) (mul_w B)

/-- Negation as a morphism in the slice category. -/
def invHom {S : Scheme.{u}} (B : AlgebraicSpace S) :
    groupSpace B ⟶ groupSpace B :=
  Over.homMk (inv B) (inv_w B)

/-- Adding zero on the left is the left unitor. -/
theorem one_mul {S : Scheme.{u}} (B : AlgebraicSpace S) :
    oneHom B ▷ groupSpace B ≫ mulMap B = (λ_ (groupSpace B)).hom := sorry

/-- Adding zero on the right is the right unitor. -/
theorem mul_one {S : Scheme.{u}} (B : AlgebraicSpace S) :
    groupSpace B ◁ oneHom B ≫ mulMap B = (ρ_ (groupSpace B)).hom := sorry

/-- Addition on the additive group space is associative. -/
theorem mul_assoc {S : Scheme.{u}} (B : AlgebraicSpace S) :
    mulMap B ▷ groupSpace B ≫ mulMap B =
      (α_ (groupSpace B) (groupSpace B) (groupSpace B)).hom ≫
        groupSpace B ◁ mulMap B ≫ mulMap B := sorry

/-- Adding the negative on the left gives the zero section. -/
theorem inv_mul {S : Scheme.{u}} (B : AlgebraicSpace S) :
    lift (invHom B) (𝟙 (groupSpace B)) ≫ mulMap B =
      toUnit (groupSpace B) ≫ oneHom B := sorry

/-- Adding the negative on the right gives the zero section. -/
theorem mul_inv {S : Scheme.{u}} (B : AlgebraicSpace S) :
    lift (𝟙 (groupSpace B)) (invHom B) ≫ mulMap B =
      toUnit (groupSpace B) ≫ oneHom B := sorry

/-- Addition on the additive group space is commutative for the canonical braiding. -/
theorem mul_comm {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (β_ (groupSpace B) (groupSpace B)).hom ≫ mulMap B = mulMap B := sorry

/-- The additive group space has its canonical group-object structure. -/
instance instGrpObjGroupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) :
    GrpObj (groupSpace B) where
  one := oneHom B
  mul := mulMap B
  inv := invHom B
  one_mul := one_mul B
  mul_one := mul_one B
  mul_assoc := mul_assoc B
  left_inv := inv_mul B
  right_inv := mul_inv B

/-- The canonical group-object structure on the additive group space is commutative. -/
instance instIsCommMonObjGroupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) :
    IsCommMonObj (groupSpace B) where
  mul_comm := mul_comm B

/-- The additive group over an algebraic space as a bundled commutative group object. -/
def commGroupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) : CommGrp (Over B) :=
  { X := groupSpace B }

/-- A point over `B` determines a global section by evaluating its additive-group coordinate. -/
def homToSection {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (point : Over.mk baseMap ⟶ groupSpace B) : Γ(T.left, ⊤) :=
  Multiplicative.toAdd (AlgebraicGeometry.AdditiveGroup.homMulEquiv S T
    (yonedaEquiv (point.left ≫ toGroupScheme B)))

/-- A global section determines a point over `B` with the specified base map. -/
def homOfSection {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (sectionValue : Γ(T.left, ⊤)) :
    Over.mk baseMap ⟶ groupSpace B :=
  let sectionPoint := yoneda.map (AlgebraicGeometry.AdditiveGroup.homOfSection S T
    (Multiplicative.ofAdd sectionValue))
  Over.homMk (prod.lift (C := (Over S)ᵒᵖ ⥤ Type u) baseMap sectionPoint)
    (prod.lift_fst (C := (Over S)ᵒᵖ ⥤ Type u) baseMap sectionPoint)

/-- Constructing a point from the section of a point recovers that point. -/
theorem homOfSection_homToSection {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (point : Over.mk baseMap ⟶ groupSpace B) :
    homOfSection B T baseMap (homToSection B T baseMap point) = point := sorry

/-- Evaluating the point associated to a section recovers that section. -/
theorem homToSection_homOfSection {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (sectionValue : Γ(T.left, ⊤)) :
    homToSection B T baseMap (homOfSection B T baseMap sectionValue) = sectionValue := sorry

/-- Scheme-valued points of the additive group space are global sections. -/
def homEquiv {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) : (Over.mk baseMap ⟶ groupSpace B) ≃ Γ(T.left, ⊤) where
  toFun := homToSection B T baseMap
  invFun := homOfSection B T baseMap
  left_inv := homOfSection_homToSection B T baseMap
  right_inv := homToSection_homOfSection B T baseMap

/-- Canonical multiplication of points corresponds to addition of global sections. -/
theorem homEquiv_add {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (first second : Over.mk baseMap ⟶ groupSpace B) :
    homEquiv B T baseMap (first * second) =
      homEquiv B T baseMap first + homEquiv B T baseMap second := sorry

/-- Scheme-valued points are group-isomorphic to additive global sections. -/
def homMulEquiv {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) :
    (Over.mk baseMap ⟶ groupSpace B) ≃* Multiplicative Γ(T.left, ⊤) where
  toFun point := Multiplicative.ofAdd (homEquiv B T baseMap point)
  invFun sectionValue := homOfSection B T baseMap (Multiplicative.toAdd sectionValue)
  left_inv := homOfSection_homToSection B T baseMap
  right_inv := homToSection_homOfSection B T baseMap
  map_mul' := homEquiv_add B T baseMap

/-- The group-valued points equivalence evaluates the second projection at the affine coordinate. -/
theorem homMulEquiv_apply {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (baseMap : ofOver T ⟶ B) (point : Over.mk baseMap ⟶ groupSpace B) :
    homMulEquiv B T baseMap point =
      AlgebraicGeometry.AdditiveGroup.homMulEquiv S T
        (yonedaEquiv (point.left ≫ toGroupScheme B)) := sorry

/-- Precomposition of points over `B` corresponds to pullback of global sections. -/
theorem homMulEquiv_naturality {S : Scheme.{u}} (B : AlgebraicSpace S)
    (T T' : Over S) (baseMap : ofOver T ⟶ B) (baseMap' : ofOver T' ⟶ B)
    (testMap : T' ⟶ T) (h_over : yoneda.map testMap ≫ baseMap = baseMap')
    (point : Over.mk baseMap ⟶ groupSpace B) :
    homMulEquiv B T' baseMap'
        (Over.homMk (V := Over.mk baseMap)
          (yoneda.map testMap : ofOver T' ⟶ ofOver T) h_over ≫ point) =
      Multiplicative.ofAdd (testMap.left.appTop
        (Multiplicative.toAdd (homMulEquiv B T baseMap point))) := sorry

end AlgebraicGeometry.AlgebraicSpace.AdditiveGroup
