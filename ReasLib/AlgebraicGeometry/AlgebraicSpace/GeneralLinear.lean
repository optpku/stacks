module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

/-!
# General linear group algebraic spaces

The general linear group algebraic space over an algebraic space `B` over `S` is the
functor-of-points product of `B` with the base-changed general linear group scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory
open CategoryTheory.Limits
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeneralLinear

/-- The general linear group scheme `GLₙ,S` viewed as an algebraic space over `S`. -/
def ofScheme (S : Scheme.{u}) (n : ℕ) [NeZero n] : AlgebraicSpace S :=
  ofOver
    (AlgebraicGeometry.GeneralLinear.baseChange
      (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X

/-- The fppf sheaf condition for the functor-of-points product defining the general linear space. -/
theorem space_isSheaf {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) := sorry

/-- The representable diagonal condition for the functor-of-points product defining the general
linear space. -/
theorem space_representableDiagonal {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    yoneda.relativelyRepresentable
      (Limits.diag (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints)) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro U x
  let F := B.functorOfPoints
  let G := (ofScheme S n).functorOfPoints
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
    (ofOver_representableDiagonal
      (AlgebraicGeometry.GeneralLinear.baseChange
        (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X)
    (@Functor.relativelyRepresentable.of_isIso _ _ _ _ yoneda _ _
      terminalDiagonalIso.hom terminalDiagonalIso.isIso_hom) (x ≫ e.hom)
  have hx' := (yoneda.relativelyRepresentable).comp_mem _ _ hx
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
  simpa only [F, G, Category.assoc, e.hom_inv_id, Category.comp_id] using hx'

/-- The étale atlas condition for the functor-of-points product defining the general linear space. -/
theorem space_hasAtlas {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶
        B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints),
      (MorphismProperty.over (@Etale)).presheaf p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  let U := B.atlas.choose
  let atlasMap := B.atlas.choose_spec.choose
  let V := (AlgebraicGeometry.GeneralLinear.baseChange
    (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X
  let p : yoneda.obj (U ⨯ V) ⟶
      B.functorOfPoints ⨯ yoneda.obj V :=
    prodComparison yoneda U V ≫ prod.map atlasMap (𝟙 (yoneda.obj V))
  refine ⟨U ⨯ V, p, ?_, ?_⟩
  · exact ⟨Functor.relativelyRepresentable.of_diag (space_representableDiagonal B n) p,
      by sorry⟩
  · sorry

/-- The general linear group algebraic space `GLₙ,B = B ×_S GLₙ,S` over `S`. -/
def space {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] : AlgebraicSpace S :=
  ofFunctor (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints)
    (space_isSheaf B n) (space_representableDiagonal B n) (space_hasAtlas B n)

/-- The functor of points of the general linear algebraic space is the product of the two factors. -/
theorem space_functorOfPoints {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (space B n).functorOfPoints = (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) := sorry

/-- The structure morphism `GLₙ,B ⟶ B`, given by the first product projection. -/
def hom {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] : space B n ⟶ B :=
  (Limits.prod.fst :
    (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶ B.functorOfPoints)

/-- The structure morphism of the general linear space is its first product projection. -/
theorem hom_eq_fst {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    hom B n = (Limits.prod.fst :
      (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶ B.functorOfPoints) := sorry

/-- The general linear group algebraic space as an object of the slice over `B`. -/
def asOver {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] : Over B :=
  Over.mk (hom B n)

/-- The underlying algebraic-space map associated to an invertible matrix of global sections. -/
def ofMatrixMap {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B)
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤)) :
    (Over.mk t).left ⟶ (asOver B n).left :=
  (Limits.prod.lift t
      (yoneda.map
        ((AlgebraicGeometry.GeneralLinear.BaseChange.homMulEquiv
            (specULiftZIsTerminal.from S) (ULift.{u} (Fin n)) T).symm M) :
        ofOver T ⟶ ofScheme S n) :
      (ofOver T).functorOfPoints ⟶
        (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints))

/-- The matrix point map is a morphism over `B`. -/
theorem ofMatrix_over {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B)
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤)) :
    ofMatrixMap n t M ≫ hom B n = t := sorry

/-- The `B`-morphism associated to an invertible matrix of global sections on `T`. -/
def ofMatrix {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B)
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤)) :
    Over.mk t ⟶ asOver B n :=
  Over.homMk
    (ofMatrixMap n t M)
    (ofMatrix_over n t M)

/-- The underlying map of `ofMatrix` is the product lift of the base point and the corresponding
point of the general linear group scheme. -/
theorem ofMatrix_left {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B)
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤)) :
    (ofMatrix n t M).left =
      (Limits.prod.lift t
        (yoneda.map
          ((AlgebraicGeometry.GeneralLinear.BaseChange.homMulEquiv
              (specULiftZIsTerminal.from S) (ULift.{u} (Fin n)) T).symm M) :
          ofOver T ⟶ ofScheme S n) :
        (ofOver T).functorOfPoints ⟶
          (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints)) := sorry

/-- The matrix associated to a morphism over `B` into the general linear algebraic space. -/
def toMatrix {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) (f : Over.mk t ⟶ asOver B n) :
    Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤) :=
  AlgebraicGeometry.GeneralLinear.BaseChange.homMulEquiv
      (specULiftZIsTerminal.from S) (ULift.{u} (Fin n)) T
    (yonedaEquiv
      ((f.left ≫ (Limits.prod.snd :
          (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
            (ofScheme S n).functorOfPoints)) :
        yoneda.obj T ⟶ (ofScheme S n).functorOfPoints))

/-- Multiplication on the general linear scheme factor, transported to algebraic-space points. -/
def ofSchemeMulApp {S : Scheme.{u}} (n : ℕ) [NeZero n] {E : AlgebraicSpace S}
    (f g : E ⟶ ofScheme S n) (T : (Over S)ᵒᵖ) :
    E.functorOfPoints.obj T ⟶ (ofScheme S n).functorOfPoints.obj T := ↾fun x ↦
    lift (f.app T x) (g.app T x) ≫
      μ[(AlgebraicGeometry.GeneralLinear.baseChange
          (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X]

/-- The naturality equation for the pointwise multiplication components. -/
theorem ofSchemeMul_naturality {S : Scheme.{u}} (n : ℕ) [NeZero n] {E : AlgebraicSpace S}
    (f g : E ⟶ ofScheme S n) {T T' : (Over S)ᵒᵖ} (k : T ⟶ T') :
    E.functorOfPoints.map k ≫ ofSchemeMulApp n f g T' =
      ofSchemeMulApp n f g T ≫ (ofScheme S n).functorOfPoints.map k := sorry

/-- Multiplication of the general linear scheme factor, transported to algebraic-space points. -/
def ofSchemeMul {S : Scheme.{u}} (n : ℕ) [NeZero n] {E : AlgebraicSpace S}
    (f g : E ⟶ ofScheme S n) : E ⟶ ofScheme S n where
  app T := ofSchemeMulApp n f g T
  naturality := fun {X Y} k => ofSchemeMul_naturality n f g (T := X) (T' := Y) k

/-- The component formula for multiplication on the general linear scheme factor. -/
theorem ofSchemeMul_app {S : Scheme.{u}} (n : ℕ) [NeZero n] {E : AlgebraicSpace S}
    (f g : E ⟶ ofScheme S n) (T : (Over S)ᵒᵖ) (x : E.functorOfPoints.obj T) :
    (ofSchemeMul n f g).app T x =
      lift (f.app T x) (g.app T x) ≫
        μ[(AlgebraicGeometry.GeneralLinear.baseChange
            (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X] := sorry

/-- The natural transformation from `B` to the general linear scheme selecting the identity
matrix at every scheme-valued point. -/
def ofSchemeOneApp {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n]
    (T : (Over S)ᵒᵖ) : B.functorOfPoints.obj T ⟶ (ofScheme S n).functorOfPoints.obj T :=
  ↾fun _ ↦
    Over.homMk T.unop.hom ≫
      η[(AlgebraicGeometry.GeneralLinear.baseChange
        (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X]
/-- Naturality of the identity-valued transformation on the general linear scheme factor. -/
theorem ofSchemeOne_naturality {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n]
    {T T' : (Over S)ᵒᵖ} (k : T ⟶ T') :
    B.functorOfPoints.map k ≫ ofSchemeOneApp B n T' =
      ofSchemeOneApp B n T ≫ (ofScheme S n).functorOfPoints.map k := sorry

/-- The natural transformation from `B` to the general linear scheme selecting the identity
matrix at every scheme-valued point. -/
def ofSchemeOne {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    B ⟶ ofScheme S n where
  app T := ofSchemeOneApp B n T
  naturality := fun {X Y} k => ofSchemeOne_naturality B n (T := X) (T' := Y) k

/-- The unit morphism of the general linear group algebraic space over `B`. -/
theorem one_over {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    ((Limits.prod.lift (𝟙 B) (ofSchemeOne B n) :
      B.functorOfPoints ⟶ (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints)) ≫ hom B n) =
      𝟙 B := sorry

/-- The unit morphism of the general linear group algebraic space over `B`. -/
def one {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    𝟙_ (Over B) ⟶ asOver B n :=
  Over.homMk
    (Limits.prod.lift (𝟙 B) (ofSchemeOne B n) :
      B.functorOfPoints ⟶ (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints))
    (one_over B n)

/-- The underlying map of the unit is the product lift of the identity and `ofSchemeOne`. -/
theorem one_left {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (one B n).left =
      (Limits.prod.lift (𝟙 B) (ofSchemeOne B n) :
        B.functorOfPoints ⟶ (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints)) := sorry

/-- The underlying algebraic-space map of multiplication on the general linear object. -/
def mulMap {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (asOver B n ⊗ asOver B n).left ⟶ (asOver B n).left :=
  (Limits.prod.lift (asOver B n ⊗ asOver B n).hom
    (ofSchemeMul n
      ((fst (asOver B n) (asOver B n)).left ≫
        (Limits.prod.snd :
          (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
            (ofScheme S n).functorOfPoints))
      ((snd (asOver B n) (asOver B n)).left ≫
        (Limits.prod.snd :
          (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
            (ofScheme S n).functorOfPoints))) :
    (asOver B n ⊗ asOver B n).left.functorOfPoints ⟶
      (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints))

/-- The multiplication map is a morphism over `B`. -/
theorem mul_over {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    mulMap B n ≫ hom B n = (asOver B n ⊗ asOver B n).hom := sorry

/-- The multiplication morphism of the general linear group algebraic space over `B`. -/
def mul {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    asOver B n ⊗ asOver B n ⟶ asOver B n :=
  Over.homMk (mulMap B n) (mul_over B n)

/-- The underlying map of multiplication is the product lift of the slice structure map and the
product of the two general-linear factors. -/
theorem mul_left {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (mul B n).left = mulMap B n := sorry

/-- The underlying algebraic-space map of inversion on the general linear object. -/
def invMap {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (asOver B n).left ⟶ (asOver B n).left :=
  (Limits.prod.lift (hom B n)
    ((Limits.prod.snd :
        (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints) ⟶
          (ofScheme S n).functorOfPoints) ≫
      (yoneda.map
        (ι[(AlgebraicGeometry.GeneralLinear.baseChange
            (specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X]) :
        ofScheme S n ⟶ ofScheme S n)) :
    (space B n).functorOfPoints ⟶
      (B.functorOfPoints ⨯ (ofScheme S n).functorOfPoints))

/-- The inverse map is a morphism over `B`. -/
theorem inv_over {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    invMap B n ≫ hom B n = hom B n := sorry

/-- The inverse morphism of the general linear group algebraic space over `B`. -/
def inv {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    asOver B n ⟶ asOver B n :=
  Over.homMk (invMap B n) (inv_over B n)

/-- The underlying map of inversion is the product lift of the structure morphism and scheme-level
inversion. -/
theorem inv_left {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (inv B n).left = invMap B n := sorry

/-- The unit law for the general linear group object over `B`. -/
theorem one_mul {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    whiskerRight (one B n) (asOver B n) ≫ mul B n =
      (leftUnitor (asOver B n)).hom := sorry

/-- The right unit law for the general linear group object over `B`. -/
theorem mul_one {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    whiskerLeft (asOver B n) (one B n) ≫ mul B n =
      (rightUnitor (asOver B n)).hom := sorry

/-- Associativity of multiplication in the general linear group object over `B`. -/
theorem mul_assoc {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    whiskerRight (mul B n) (asOver B n) ≫ mul B n =
      (associator (asOver B n) (asOver B n) (asOver B n)).hom ≫
        whiskerLeft (asOver B n) (mul B n) ≫ mul B n := sorry

/-- The left inverse law for the general linear group object over `B`. -/
theorem left_inv {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    CartesianMonoidalCategory.lift (inv B n) (𝟙 (asOver B n)) ≫ mul B n =
      SemiCartesianMonoidalCategory.toUnit (asOver B n) ≫ one B n := sorry

/-- The right inverse law for the general linear group object over `B`. -/
theorem right_inv {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    CartesianMonoidalCategory.lift (𝟙 (asOver B n)) (inv B n) ≫ mul B n =
      SemiCartesianMonoidalCategory.toUnit (asOver B n) ≫ one B n := sorry

/-- The canonical group-object structure on the general linear object over `B`. -/
instance instGrpObj_asOver {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    GrpObj (asOver B n) where
  one := one B n
  mul := mul B n
  one_mul := one_mul B n
  mul_one := mul_one B n
  mul_assoc := mul_assoc B n
  inv := inv B n
  left_inv := left_inv B n
  right_inv := right_inv B n

/-- The group algebraic space `GLₙ,B` over `B`, with underlying object `asOver B n`. -/
def groupSpace {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    GroupAlgebraicSpace B :=
  ⟨asOver B n⟩

/-- The underlying object of the general linear group algebraic space is `asOver B n`. -/
theorem groupSpace_X {S : Scheme.{u}} (B : AlgebraicSpace S) (n : ℕ) [NeZero n] :
    (groupSpace B n).X = asOver B n := sorry

/-- The inverse point construction is inverse to evaluation at the associated matrix. -/
theorem ofMatrix_toMatrix {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) (f : Over.mk t ⟶ asOver B n) :
    ofMatrix n t (toMatrix n t f) = f := sorry

/-- Evaluation at a morphism recovers the original matrix point. -/
theorem toMatrix_ofMatrix {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B)
    (M : Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤)) :
    toMatrix n t (ofMatrix n t M) = M := sorry

/-- Multiplication of morphisms over `B` is transported to matrix multiplication. -/
theorem toMatrix_mul {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) (f g : Over.mk t ⟶ asOver B n) :
    toMatrix n t (f * g) = toMatrix n t f * toMatrix n t g := sorry

/-- The multiplicative equivalence between points over `B` and invertible matrices. -/
def homOverMulEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) :
    (Over.mk t ⟶ asOver B n) ≃*
      Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤) where
  toFun := toMatrix n t
  invFun := ofMatrix n t
  left_inv := ofMatrix_toMatrix n t
  right_inv := toMatrix_ofMatrix n t
  map_mul' := toMatrix_mul n t

/-- The forward map of `homOverMulEquiv n t` is `toMatrix n t`. -/
theorem homOverMulEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T : Over S} (t : ofOver T ⟶ B) (f : Over.mk t ⟶ asOver B n) :
    homOverMulEquiv n t f = toMatrix n t f := sorry

/-- The slice morphism induced by precomposition with a morphism of schemes over `S`. -/
def overMap {S : Scheme.{u}} {T T' : Over S} (g : T' ⟶ T) :
    ofOver T' ⟶ ofOver T := yoneda.map g

/-- The slice morphism induced by precomposition with a morphism of schemes over `S`. -/
def sliceMap {S : Scheme.{u}} {B : AlgebraicSpace S} {T T' : Over S}
    (g : T' ⟶ T) (t : ofOver T ⟶ B) :
    (Over.mk (overMap g ≫ t) : Over B) ⟶
      (Over.mk t : Over B) :=
  Over.homMk (overMap g) rfl

/-- Naturality of the matrix-valued points equivalence under precomposition by a scheme morphism
over `B`. -/
theorem homOverMulEquiv_naturality {S : Scheme.{u}} {B : AlgebraicSpace S} (n : ℕ) [NeZero n]
    {T T' : Over S} (g : T' ⟶ T) (t : ofOver T ⟶ B)
    (h : Over.mk t ⟶ asOver B n) :
    homOverMulEquiv n (overMap g ≫ t) (sliceMap g t ≫ h) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.left.op).hom (homOverMulEquiv n t h) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeneralLinear
