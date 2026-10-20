/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme
public import ReasLib.CategoryTheory.Monoidal.PresheafSlice

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RootsOfUnity

/-- The representing roots functor is identified with the functor of points of its scheme. -/
def baseChangeToOfOver (n : ℕ) [NeZero n] {S : Scheme.{u}} :
    functorOfPoints S n ⋙ forget CommGrpCat ⟶
      (ofOver (baseChange n S).X).functorOfPoints :=
  (BaseChange.representableBy n S).toIso.inv ≫
    eqToHom (AlgebraicSpace.ofOver_functorOfPoints (baseChange n S).X).symm

/-- The functor of points of the representing scheme is identified with the roots functor. -/
def ofOverToBaseChange (n : ℕ) [NeZero n] {S : Scheme.{u}} :
    (ofOver (baseChange n S).X).functorOfPoints ⟶
      functorOfPoints S n ⋙ forget CommGrpCat :=
  eqToHom (AlgebraicSpace.ofOver_functorOfPoints (baseChange n S).X) ≫
    (BaseChange.representableBy n S).toIso.hom

namespace Space

/-- The pointwise product of the functor of points of `B` with the roots-of-unity functor. -/
def presheaf (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  MonoidalCategoryStruct.tensorObj B.functorOfPoints
    (functorOfPoints S n ⋙ forget CommGrpCat)

/-- The product presheaf satisfies fppf descent. -/
theorem isSheaf (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (presheaf n B) := sorry

/-- The diagonal of the product presheaf is representable. -/
theorem representableDiagonal (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    yoneda.relativelyRepresentable (Limits.diag (presheaf n B)) := sorry

/-- The product presheaf has a representable étale locally-surjective atlas. -/
theorem atlas (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ presheaf n B),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end Space

/-- The product presheaf is an algebraic space. -/
def algebraicSpace (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    AlgebraicSpace S :=
  AlgebraicSpace.ofFunctor (Space.presheaf n B) (Space.isSheaf n B)
    (Space.representableDiagonal n B) (Space.atlas n B)

/-- The structure morphism of the roots-of-unity algebraic space is its first projection. -/
def algebraicSpace_fst (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    algebraicSpace n B ⟶ B :=
  SemiCartesianMonoidalCategory.fst B.functorOfPoints
    (functorOfPoints S n ⋙ forget CommGrpCat)

/-- The second projection of the product presheaf is transported to the representing scheme. -/
def algebraicSpace_snd (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    algebraicSpace n B ⟶ ofOver (baseChange n S).X :=
  (SemiCartesianMonoidalCategory.snd B.functorOfPoints
      (functorOfPoints S n ⋙ forget CommGrpCat) ≫
    baseChangeToOfOver (S := S) n :
      (algebraicSpace n B).functorOfPoints ⟶
        (ofOver (baseChange n S).X).functorOfPoints)

/-- The roots-of-unity algebraic space viewed as an object over `B`. -/
def algebraicSpaceOver (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Over B :=
  Over.mk (algebraicSpace_fst n B)

/-- The product lift into the roots-of-unity algebraic space. -/
def algebraicSpaceLift (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X : AlgebraicSpace S} (f : X ⟶ B) (g : X ⟶ ofOver (baseChange n S).X) :
    X ⟶ algebraicSpace n B :=
  CartesianMonoidalCategory.lift (C := (Over S)ᵒᵖ ⥤ Type u)
    (f : X.functorOfPoints ⟶ B.functorOfPoints)
    ((g : X.functorOfPoints ⟶ (ofOver (baseChange n S).X).functorOfPoints) ≫
      ofOverToBaseChange (S := S) n)

/-- The first projection of the explicit product lift is the given map. -/
theorem algebraicSpaceLift_fst (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X : AlgebraicSpace S} (f : X ⟶ B) (g : X ⟶ ofOver (baseChange n S).X) :
    algebraicSpaceLift n B f g ≫ algebraicSpace_fst n B = f := sorry

/-- The second projection of the explicit product lift is the given map. -/
theorem algebraicSpaceLift_snd (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X : AlgebraicSpace S} (f : X ⟶ B) (g : X ⟶ ofOver (baseChange n S).X) :
    algebraicSpaceLift n B f g ≫ algebraicSpace_snd n B = g := sorry

/-- The explicit product lift is unique with its two projections. -/
theorem algebraicSpaceLift_uniq (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X : AlgebraicSpace S} (f : X ⟶ B) (g : X ⟶ ofOver (baseChange n S).X)
    (m : X ⟶ algebraicSpace n B)
    (hm₁ : m ≫ algebraicSpace_fst n B = f)
    (hm₂ : m ≫ algebraicSpace_snd n B = g) :
    m = algebraicSpaceLift n B f g := sorry

/-- The product characterization of the roots-of-unity algebraic space. -/
def algebraicSpaceIsLimit (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    IsLimit (BinaryFan.mk (algebraicSpace_fst n B) (algebraicSpace_snd n B)) :=
  BinaryFan.IsLimit.mk _ (algebraicSpaceLift n B) (algebraicSpaceLift_fst n B)
    (algebraicSpaceLift_snd n B) (algebraicSpaceLift_uniq n B)

namespace Space

/-- The product presheaf in the slice over the functor of points of `B`. -/
def «over» (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    Over B.functorOfPoints :=
  Over.mk (algebraicSpace_fst n B)

/-- The unit point at a test object is the pair `(b, 1)`. -/
def oneApp (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    (X : (Over S)ᵒᵖ) : B.functorOfPoints.obj X ⟶ (presheaf n B).obj X :=
  ↾fun b => (b, 1)

/-- The unit pointwise map is natural in the test object. -/
theorem one_naturality (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) :
    B.functorOfPoints.map f ≫ oneApp n B Y =
      oneApp n B X ≫ (presheaf n B).map f := sorry

/-- The natural transformation underlying the unit of the relative group object. -/
def oneLeft (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    B.functorOfPoints ⟶ presheaf n B where
  app := oneApp n B
  naturality := fun {X Y} f => one_naturality n B f

/-- The unit point lies over the base point. -/
theorem one_over (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    oneLeft n B ≫ algebraicSpace_fst n B = (𝟙_ (Over B.functorOfPoints)).hom := sorry


/-- The pointwise multiplication map on the product presheaf. -/
def mulApp (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    (X : (Over S)ᵒᵖ) :
    (MonoidalCategoryStruct.tensorObj («over» n B) («over» n B)).left.obj X ⟶ (presheaf n B).obj X :=
  ↾fun z =>
    let x := (pullback.fst («over» n B).hom («over» n B).hom).app X z
    let y := (pullback.snd («over» n B).hom («over» n B).hom).app X z
    (x.1, x.2 * y.2)

/-- Multiplication on the product presheaf is natural in the test object. -/
theorem mul_naturality (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) :
    (MonoidalCategoryStruct.tensorObj («over» n B) («over» n B)).left.map f ≫ mulApp n B Y =
      mulApp n B X ≫ (presheaf n B).map f := sorry

/-- The natural transformation underlying multiplication on the product presheaf. -/
def mulLeft (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (MonoidalCategoryStruct.tensorObj («over» n B) («over» n B)).left ⟶ presheaf n B where
  app := mulApp n B
  naturality := fun {X Y} f => mul_naturality n B f

/-- Multiplication on the product presheaf preserves the map to `B`. -/
theorem mul_over (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    mulLeft n B ≫ algebraicSpace_fst n B =
      (MonoidalCategoryStruct.tensorObj («over» n B) («over» n B)).hom := sorry

/-- The pointwise inversion map on the product presheaf. -/
def invApp (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    (X : (Over S)ᵒᵖ) : (presheaf n B).obj X ⟶ (presheaf n B).obj X :=
  ↾fun z => (z.1, z.2⁻¹)

/-- Inversion on the product presheaf is natural in the test object. -/
theorem inv_naturality (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) :
    (presheaf n B).map f ≫ invApp n B Y =
      invApp n B X ≫ (presheaf n B).map f := sorry

/-- The natural transformation underlying inversion on the product presheaf. -/
def invLeft (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    presheaf n B ⟶ presheaf n B where
  app := invApp n B
  naturality := fun {X Y} f => inv_naturality n B f

/-- Inversion on the product presheaf preserves the map to `B`. -/
theorem inv_over (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    invLeft n B ≫ algebraicSpace_fst n B = («over» n B).hom := sorry

/-- The multiplication morphism of the relative roots-of-unity group object. -/
def mul (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    MonoidalCategoryStruct.tensorObj («over» n B) («over» n B) ⟶ «over» n B :=
  Over.homMk (mulLeft n B) (mul_over n B)

/-- The unit morphism of the relative roots-of-unity group object. -/
def one (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    𝟙_ (Over B.functorOfPoints) ⟶ «over» n B :=
  Over.homMk (oneLeft n B) (one_over n B)

/-- The inverse morphism of the relative roots-of-unity group object. -/
def inv (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    «over» n B ⟶ «over» n B :=
  Over.homMk (invLeft n B) (inv_over n B)

/-- The relative unit law for multiplication. -/
theorem one_mul (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (one n B ▷ «over» n B) ≫ mul n B = (λ_ («over» n B)).hom := sorry

/-- The relative right-unit law for multiplication. -/
theorem mul_one (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    («over» n B ◁ one n B) ≫ mul n B = (ρ_ («over» n B)).hom := sorry

/-- The relative associativity law for multiplication. -/
theorem mul_assoc (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (mul n B ▷ «over» n B) ≫ mul n B =
      (α_ («over» n B) («over» n B) («over» n B)).hom ≫ («over» n B ◁ mul n B) ≫ mul n B := sorry

/-- The left inverse law for the relative roots-of-unity group object. -/
theorem left_inv (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CartesianMonoidalCategory.lift (inv n B) (𝟙 («over» n B)) ≫ mul n B =
      CartesianMonoidalCategory.toUnit («over» n B) ≫ one n B := sorry

/-- The right inverse law for the relative roots-of-unity group object. -/
theorem right_inv (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CartesianMonoidalCategory.lift (𝟙 («over» n B)) (inv n B) ≫ mul n B =
      CartesianMonoidalCategory.toUnit («over» n B) ≫ one n B := sorry

/-- The relative multiplication is commutative. -/
theorem mul_comm (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (β_ («over» n B) («over» n B)).hom ≫ mul n B = mul n B := sorry

end Space

/-- The commutative group object carried by the relative roots-of-unity space. -/
noncomputable instance instCommGrpObj (n : ℕ) [NeZero n] {S : Scheme.{u}}
    (B : AlgebraicSpace S) : CommGrpObj (Space.«over» n B) where
  one := Space.one n B
  mul := Space.mul n B
  one_mul := Space.one_mul n B
  mul_one := Space.mul_one n B
  mul_assoc := Space.mul_assoc n B
  inv := Space.inv n B
  left_inv := Space.left_inv n B
  right_inv := Space.right_inv n B
  mul_comm := Space.mul_comm n B

/-- The relative roots-of-unity group object. -/
def groupSpace (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CommGrp (Over B.functorOfPoints) :=
  { X := Space.«over» n B }

/-- The underlying object of `groupSpace n B` is the relative algebraic space over `B`. -/
theorem groupSpace_left (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace n B).X = Space.«over» n B := rfl

/-- The structure morphism of `groupSpace n B` is the first product projection. -/
theorem groupSpace_hom (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) :
    (groupSpace n B).X.hom = algebraicSpace_fst n B := rfl

namespace Space

/-- The root attached to a point is the second coordinate at the identity of `T`. -/
def toRoot (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints)
    (f : Over.mk t ⟶ Space.«over» n B) : rootsOfUnity n Γ(T.left, ⊤) :=
  (f.left.app (op T) (𝟙 T)).2

/-- The pointwise root map is multiplicative. -/
theorem toRoot_mul (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints)
    (f g : Over.mk t ⟶ Space.«over» n B) :
    toRoot n B T t (f * g) = toRoot n B T t f * toRoot n B T t g := sorry

/-- The pointwise map associated to a prescribed root. -/
def ofRootApp (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤))
    (X : (Over S)ᵒᵖ) : (yoneda.obj T).obj X ⟶ (presheaf n B).obj X :=
  ↾fun q => (t.app X q, restrictRootsOfUnity (Scheme.Γ.map q.left.op).hom n ζ)

/-- The prescribed-root map is natural in the test object. -/
theorem ofRoot_naturality (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤))
    {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) :
    (yoneda.obj T).map f ≫ ofRootApp n B T t ζ Y =
      ofRootApp n B T t ζ X ≫ (presheaf n B).map f := sorry

/-- The natural transformation associated to a prescribed root. -/
def ofRootLeft (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    yoneda.obj T ⟶ presheaf n B where
  app := ofRootApp n B T t ζ
  naturality := fun {X Y} f => ofRoot_naturality n B T t ζ f

/-- The prescribed-root transformation lies over the chosen map to `B`. -/
theorem ofRoot_over (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    ofRootLeft n B T t ζ ≫ algebraicSpace_fst n B = t := sorry

/-- The morphism over `B` associated to a prescribed root. -/
def ofRoot (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    Over.mk t ⟶ Space.«over» n B :=
  Over.homMk (ofRootLeft n B T t ζ) (ofRoot_over n B T t ζ)

/-- The prescribed-root construction recovers the original root. -/
theorem ofRoot_toRoot (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    toRoot n B T t (ofRoot n B T t ζ) = ζ := sorry

/-- Every point over `B` is recovered from its second coordinate. -/
theorem toRoot_ofRoot (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints)
    (f : Over.mk t ⟶ Space.«over» n B) :
    ofRoot n B T t (toRoot n B T t f) = f := sorry

/-- Scheme-valued points over `B` are equivalent to roots of unity. -/
def homEquiv (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) :
    (Over.mk t ⟶ Space.«over» n B) ≃ rootsOfUnity n Γ(T.left, ⊤) where
  toFun := toRoot n B T t
  invFun := ofRoot n B T t
  left_inv := toRoot_ofRoot n B T t
  right_inv := ofRoot_toRoot n B T t

end Space

/-- The multiplicative point classification of the relative roots-of-unity group space. -/
def homMulEquiv (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints) :
    (Over.mk t ⟶ (groupSpace n B).X) ≃* rootsOfUnity n Γ(T.left, ⊤) where
  toEquiv := Space.homEquiv n B T t
  map_mul' := Space.toRoot_mul n B T t

/-- The multiplicative point classification evaluates the second coordinate at the identity. -/
theorem homMulEquiv_apply (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S) (T : Over S)
    (t : yoneda.obj T ⟶ B.functorOfPoints)
    (f : Over.mk t ⟶ (groupSpace n B).X) :
    homMulEquiv n B T t f = Space.toRoot n B T t f := rfl

/-- The relative point classification is natural under compatible morphisms of test schemes. -/
theorem homMulEquiv_naturality (n : ℕ) [NeZero n] {S : Scheme.{u}} (B : AlgebraicSpace S)
    {T T' : Over S} (g : T' ⟶ T) (t : yoneda.obj T ⟶ B.functorOfPoints)
    (f : Over.mk t ⟶ (groupSpace n B).X)
    (f' : Over.mk (yoneda.map g ≫ t) ⟶ (groupSpace n B).X)
    (h : f'.left = yoneda.map g ≫ f.left) :
    homMulEquiv n B T' (yoneda.map g ≫ t) f' =
      restrictRootsOfUnity (Scheme.Γ.map g.left.op).hom n (homMulEquiv n B T t f) := sorry

end AlgebraicGeometry.RootsOfUnity
