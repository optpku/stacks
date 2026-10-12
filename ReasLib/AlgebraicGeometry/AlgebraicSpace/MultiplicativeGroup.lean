/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-! The multiplicative group over an algebraic space and its global-unit points. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
open CartesianMonoidalCategory (lift fst snd)
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup

/-- The multiplicative group scheme over `S`, viewed as an algebraic space. -/
def ofScheme (S : Scheme.{u}) : AlgebraicSpace S :=
  ofOver (AlgebraicGeometry.MultiplicativeGroup.baseChange S).X

/-- The multiplicative group space over a scheme is represented by its group scheme. -/
theorem ofScheme_eq (S : Scheme.{u}) :
    ofScheme S = ofOver (AlgebraicGeometry.MultiplicativeGroup.baseChange S).X := sorry

/-- The product of the functors of points of `B` and the multiplicative group is an fppf sheaf. -/
theorem space_isSheaf {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints) := sorry

/-- The product of `B` with the multiplicative group has representable diagonal. -/
theorem space_representableDiagonal {S : Scheme.{u}} (B : AlgebraicSpace S) :
    yoneda.relativelyRepresentable
      (Limits.diag (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints)) := sorry

/-- The product of `B` with the multiplicative group admits an étale locally-surjective atlas. -/
theorem space_atlas {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ B.functorOfPoints ⨯ (ofScheme S).functorOfPoints),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The multiplicative group space over `B` is the product `B ×_S 𝔾ₘ[S]`. -/
def space {S : Scheme.{u}} (B : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints)
    (space_isSheaf B) (space_representableDiagonal B) (space_atlas B)

/-- The functor of points of the multiplicative group over `B` is the presheaf product. -/
theorem space_functorOfPoints {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (space B).functorOfPoints = (B.functorOfPoints ⨯ (ofScheme S).functorOfPoints) := sorry

/-- The structure morphism to `B` is the first presheaf-product projection. -/
def hom {S : Scheme.{u}} (B : AlgebraicSpace S) : space B ⟶ B :=
  (Limits.prod.fst : B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ B.functorOfPoints)

/-- The structure morphism of the multiplicative group is the first projection. -/
theorem hom_eq_fst {S : Scheme.{u}} (B : AlgebraicSpace S) :
    hom B = (Limits.prod.fst : B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶
      B.functorOfPoints) := sorry

/-- The multiplicative group over `B` as an object of the slice category. -/
def asOver {S : Scheme.{u}} (B : AlgebraicSpace S) : Over B :=
  Over.mk (hom B)

/-- The slice object of the multiplicative group is its first projection to the base. -/
theorem asOver_eq {S : Scheme.{u}} (B : AlgebraicSpace S) :
    asOver B = Over.mk (hom B) := sorry

/-- The structure map of the slice object is the first projection. -/
theorem asOver_hom {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (asOver B).hom = hom B := sorry

/-- Pairing a point of `B` with a global unit gives a map over `B`. -/
theorem ofUnit_w {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (unit : Γ(T.left, ⊤)ˣ) :
    Limits.prod.lift (X := B.functorOfPoints) t
        (yoneda.map ((AlgebraicGeometry.MultiplicativeGroup.baseChangeHomEquiv S T).symm unit)) ≫
      hom B = t := sorry

/-- The morphism to the multiplicative group over `B` associated with a global unit. -/
def ofUnit {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B)
    (unit : Γ(T.left, ⊤)ˣ) : Over.mk t ⟶ asOver B :=
  Over.homMk (Limits.prod.lift (X := B.functorOfPoints) t
    (yoneda.map ((AlgebraicGeometry.MultiplicativeGroup.baseChangeHomEquiv S T).symm unit)))
    (ofUnit_w t unit)

/-- The underlying map associated with a global unit pairs the base point with its Yoneda map. -/
theorem ofUnit_left {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (unit : Γ(T.left, ⊤)ˣ) :
    (ofUnit t unit).left = Limits.prod.lift (X := B.functorOfPoints) t
      (yoneda.map ((AlgebraicGeometry.MultiplicativeGroup.baseChangeHomEquiv S T).symm unit)) := sorry

/-- The global unit extracted from the second projection of a morphism over `B`. -/
def toUnit {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B)
    (point : Over.mk t ⟶ asOver B) : Γ(T.left, ⊤)ˣ :=
  AlgebraicGeometry.MultiplicativeGroup.baseChangeHomEquiv S T
    (yonedaEquiv (point.left ≫ Limits.prod.snd :
      yoneda.obj T ⟶ yoneda.obj (AlgebraicGeometry.MultiplicativeGroup.baseChange S).X))

/-- Constructing a point from its extracted unit recovers the original morphism over `B`. -/
theorem ofUnit_toUnit {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (point : Over.mk t ⟶ asOver B) :
    ofUnit t (toUnit t point) = point := sorry

/-- Extracting the unit of the point associated with a global unit recovers that unit. -/
theorem toUnit_ofUnit {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (unit : Γ(T.left, ⊤)ˣ) :
    toUnit t (ofUnit t unit) = unit := sorry

/-- Morphisms over `B` to its multiplicative group are equivalent to global units. -/
def homOverEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S} (t : ofOver T ⟶ B) :
    (Over.mk t ⟶ asOver B) ≃ Γ(T.left, ⊤)ˣ :=
  Equiv.mk (toUnit t) (ofUnit t) (ofUnit_toUnit t) (toUnit_ofUnit t)

/-- The points-to-units equivalence extracts the unit from the second projection. -/
theorem homOverEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (point : Over.mk t ⟶ asOver B) :
    homOverEquiv t point = toUnit t point := sorry

/-- Pointwise multiplication into the multiplicative group commutes with restriction. -/
theorem ofSchemeMul_naturality {S : Scheme.{u}} {E : AlgebraicSpace S}
    (first second : E ⟶ ofScheme S) {T T' : (Over S)ᵒᵖ} (map : T ⟶ T') :
    E.functorOfPoints.map map ≫
        (↾fun point ↦ lift (first.app T' point) (second.app T' point) ≫
          μ[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]) =
      (↾fun point ↦ lift (first.app T point) (second.app T point) ≫
        μ[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]) ≫
          (ofScheme S).functorOfPoints.map map := sorry

/-- Multiplication of morphisms into the multiplicative group, induced by scheme multiplication. -/
def ofSchemeMul {S : Scheme.{u}} {E : AlgebraicSpace S} (first second : E ⟶ ofScheme S) :
    E ⟶ ofScheme S where
  app T := ↾fun point ↦ lift (first.app T point) (second.app T point) ≫
    μ[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]
  naturality := fun _ _ map ↦ ofSchemeMul_naturality first second map

/-- Pointwise multiplication is Cartesian pairing followed by scheme multiplication. -/
theorem ofSchemeMul_app {S : Scheme.{u}} {E : AlgebraicSpace S}
    (first second : E ⟶ ofScheme S) (T : (Over S)ᵒᵖ) (point : E.functorOfPoints.obj T) :
    (ofSchemeMul first second).app T point = lift (first.app T point) (second.app T point) ≫
      μ[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X] := sorry

/-- The constant unit section commutes with restriction of scheme-valued points. -/
theorem ofSchemeOne_naturality {S : Scheme.{u}} (E : AlgebraicSpace S)
    {T T' : (Over S)ᵒᵖ} (map : T ⟶ T') :
    E.functorOfPoints.map map ≫
        (↾fun _ ↦ Over.homMk T'.unop.hom ≫
          η[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]) =
      (↾fun _ ↦ Over.homMk T.unop.hom ≫
        η[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]) ≫
          (ofScheme S).functorOfPoints.map map := sorry

/-- The constant unit morphism from an algebraic space to the multiplicative group scheme. -/
def ofSchemeOne {S : Scheme.{u}} (E : AlgebraicSpace S) : E ⟶ ofScheme S where
  app T := ↾fun _ ↦ Over.homMk T.unop.hom ≫
    η[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X]
  naturality := fun _ _ map ↦ ofSchemeOne_naturality E map

/-- Pairing the identity of `B` with the unit section gives a morphism over `B`. -/
theorem oneHom_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Limits.prod.lift (X := B.functorOfPoints) (𝟙 B.functorOfPoints) (ofSchemeOne B) ≫ hom B = 𝟙 B := sorry

/-- The unit of the multiplicative group over `B`. -/
def oneHom {S : Scheme.{u}} (B : AlgebraicSpace S) : 𝟙_ (Over B) ⟶ asOver B :=
  Over.homMk (Limits.prod.lift (X := B.functorOfPoints) (𝟙 B.functorOfPoints) (ofSchemeOne B)) (oneHom_w B)

/-- The underlying unit morphism pairs the identity with the constant unit section. -/
theorem oneHom_left {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (oneHom B).left = Limits.prod.lift (X := B.functorOfPoints) (𝟙 B.functorOfPoints) (ofSchemeOne B) := sorry

/-- Multiplying two multiplicative-group points preserves their common base point. -/
theorem mulHom_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Limits.prod.lift (X := B.functorOfPoints) (asOver B ⊗ asOver B).hom
        (ofSchemeMul
          ((fst (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
            B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))
          ((snd (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
            B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))) ≫
      hom B = (asOver B ⊗ asOver B).hom := sorry

/-- Multiplication of the multiplicative group over `B`. -/
def mulHom {S : Scheme.{u}} (B : AlgebraicSpace S) :
    asOver B ⊗ asOver B ⟶ asOver B :=
  Over.homMk (Limits.prod.lift (X := B.functorOfPoints) (asOver B ⊗ asOver B).hom
    (ofSchemeMul
      ((fst (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))
      ((snd (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))))
    (mulHom_w B)

/-- Multiplication pairs the tensor structure map with pointwise scheme multiplication. -/
theorem mulHom_left {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (mulHom B).left = Limits.prod.lift (X := B.functorOfPoints) (asOver B ⊗ asOver B).hom
      (ofSchemeMul
        ((fst (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
          B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))
        ((snd (asOver B) (asOver B)).left ≫ (Limits.prod.snd :
          B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints))) := sorry

/-- Scheme inversion on the second projection preserves the base point. -/
theorem invHom_w {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Limits.prod.lift (X := B.functorOfPoints) (hom B)
        ((Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints) ≫
          yoneda.map (ι[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X])) ≫
      hom B = hom B := sorry

/-- Inversion of the multiplicative group over `B`. -/
def invHom {S : Scheme.{u}} (B : AlgebraicSpace S) : asOver B ⟶ asOver B :=
  Over.homMk (Limits.prod.lift (X := B.functorOfPoints) (hom B)
    ((Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints) ≫
          yoneda.map (ι[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X])))
    (invHom_w B)

/-- The underlying inverse pairs the base map with scheme inversion on the second projection. -/
theorem invHom_left {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (invHom B).left = Limits.prod.lift (X := B.functorOfPoints) (hom B)
      ((Limits.prod.snd :
        B.functorOfPoints ⨯ (ofScheme S).functorOfPoints ⟶ (ofScheme S).functorOfPoints) ≫
          yoneda.map (ι[(AlgebraicGeometry.MultiplicativeGroup.baseChange S).X])) := sorry

/-- The unit followed by multiplication on the left is the left unitor. -/
theorem one_mul {S : Scheme.{u}} (B : AlgebraicSpace S) :
    oneHom B ▷ asOver B ≫ mulHom B = (λ_ (asOver B)).hom := sorry

/-- The unit followed by multiplication on the right is the right unitor. -/
theorem mul_one {S : Scheme.{u}} (B : AlgebraicSpace S) :
    asOver B ◁ oneHom B ≫ mulHom B = (ρ_ (asOver B)).hom := sorry

/-- Multiplication of the multiplicative group over an algebraic space is associative. -/
theorem mul_assoc {S : Scheme.{u}} (B : AlgebraicSpace S) :
    mulHom B ▷ asOver B ≫ mulHom B =
      (α_ (asOver B) (asOver B) (asOver B)).hom ≫ asOver B ◁ mulHom B ≫ mulHom B := sorry

/-- Multiplication of the inverse on the left with the original point gives the unit. -/
theorem left_inv {S : Scheme.{u}} (B : AlgebraicSpace S) :
    lift (invHom B) (𝟙 (asOver B)) ≫ mulHom B =
      CartesianMonoidalCategory.toUnit (asOver B) ≫ oneHom B := sorry

/-- Multiplication of the original point with its inverse on the right gives the unit. -/
theorem right_inv {S : Scheme.{u}} (B : AlgebraicSpace S) :
    lift (𝟙 (asOver B)) (invHom B) ≫ mulHom B =
      CartesianMonoidalCategory.toUnit (asOver B) ≫ oneHom B := sorry

/-- The canonical group-object structure on the multiplicative group over `B`. -/
instance instGrpObj_asOver {S : Scheme.{u}} (B : AlgebraicSpace S) :
    GrpObj (asOver B) where
  one := oneHom B
  mul := mulHom B
  inv := invHom B
  one_mul := one_mul B
  mul_one := mul_one B
  mul_assoc := mul_assoc B
  left_inv := left_inv B
  right_inv := right_inv B

/-- The multiplicative group as a bundled group algebraic space over `B`. -/
def groupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) : GroupAlgebraicSpace B :=
  ⟨asOver B⟩

/-- The underlying slice object of the multiplicative group is its first projection. -/
theorem groupSpace_X {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace B).X = asOver B := sorry

/-- Extracting global units respects multiplication of morphisms over `B`. -/
theorem toUnit_mul {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (first second : Over.mk t ⟶ asOver B) :
    toUnit t (first * second) = toUnit t first * toUnit t second := sorry

/-- Morphisms over `B` to the multiplicative group are multiplicatively equivalent to global units. -/
def homOverMulEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) : (Over.mk t ⟶ asOver B) ≃* Γ(T.left, ⊤)ˣ where
  toEquiv := homOverEquiv t
  map_mul' := toUnit_mul t

/-- The multiplicative equivalence extracts the global unit from the second projection. -/
theorem homOverMulEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} {T : Over S}
    (t : ofOver T ⟶ B) (point : Over.mk t ⟶ asOver B) :
    homOverMulEquiv t point = toUnit t point := sorry

/-- The equivalence with global units commutes with precomposition over `B` and pullback of units. -/
theorem homOverMulEquiv_comp {S : Scheme.{u}} {B : AlgebraicSpace S} {T T' : Over S}
    (map : T ⟶ T') (t : ofOver T ⟶ B) (t' : ofOver T' ⟶ B)
    (ht : yoneda.map map ≫ t' = t) (point : Over.mk t' ⟶ asOver B) :
    homOverMulEquiv t (Over.homMk (V := Over.mk t') (yoneda.map map) ht ≫ point) =
      (AlgebraicGeometry.MultiplicativeGroup.points S).map map.op
        (homOverMulEquiv t' point) := sorry

end AlgebraicGeometry.AlgebraicSpace.MultiplicativeGroup
