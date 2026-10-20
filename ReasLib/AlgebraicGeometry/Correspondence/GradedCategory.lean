/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Category
public import ReasLib.AlgebraicGeometry.Correspondence.Monoidal
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.TateGraded

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The category of graded rational Chow correspondences: an object is a smooth
projective scheme together with its integral Tate index. -/
def GradedCategory (k : Type u) [Field k] := Category k × ℤ

/-- The graded-correspondence carrier is the product of the correspondence category
with the integral grading. -/
theorem gradedCategory_def (k : Type u) [Field k] :
    GradedCategory k = (Category k × ℤ) :=
  rfl

namespace GradedCategory

/-- A smooth projective scheme placed in Tate degree `n`. -/
def ofScheme (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n : ℤ) : GradedCategory k :=
  (⟨X, ⟨inferInstance, inferInstance⟩⟩, n)

/-- The underlying scheme of `ofScheme X n` is `X`. -/
theorem ofScheme_scheme (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom]
    (n : ℤ) : (ofScheme X n).1.scheme = X :=
  rfl

/-- Tensor product of graded correspondences, adding their Tate indices. -/
def tensorObj (X Y : GradedCategory k) : GradedCategory k :=
  (Category.product X.1 Y.1, X.2 + Y.2)

/-- The Tate index of a tensor product is the sum of the two indices. -/
theorem tensorObj_twist (X Y : GradedCategory k) :
    (tensorObj X Y).2 = X.2 + Y.2 :=
  rfl

/-- The tensor unit is the point over `k` in Tate degree zero. -/
def tensorUnit (k : Type u) [Field k] : GradedCategory k :=
  ofScheme (SchemeOverField.point k) 0

/-- The tensor unit has Tate index zero. -/
theorem tensorUnit_twist (k : Type u) [Field k] : (tensorUnit k).2 = 0 :=
  rfl

/-- Equality used to place identity correspondences in the graded Hom type. -/
theorem degree_id (n : ℤ) : 0 = n - n :=
  TateGraded.degree_id n

/-- Equality identifying the sum of composable correspondence degrees. -/
theorem degree_comp (a b c : ℤ) : (b - a) + (c - b) = c - a :=
  TateGraded.degree_comp a b c

/-- Homogeneous rational correspondences of Tate degree `Y.2 - X.2`. -/
abbrev gradedHom (X Y : GradedCategory k) :=
  Rational X.1.scheme Y.1.scheme (Y.2 - X.2)

/-- The identity graded correspondence, obtained by transporting the graph of the
identity morphism to Tate degree zero. -/
noncomputable def gradedId (X : GradedCategory k) : gradedHom X X :=
  castDegree (degree_id X.2)
    (rationalGraphIso X.1 X.1 (Iso.refl X.1.scheme))

/-- Composition of homogeneous rational correspondences with degree transport. -/
def gradedComp {X Y Z : GradedCategory k}
    (f : gradedHom X Y) (g : gradedHom Y Z) : gradedHom X Z :=
  castDegree (degree_comp X.2 Y.2 Z.2)
    (composition X.1.scheme Y.1.scheme Z.1.scheme (Y.2 - X.2) (Z.2 - Y.2) f g)

/-- Degree-zero correspondences between equally twisted objects are graded morphisms. -/
def homOfDegreeZero {X Y : GradedCategory k} (h : X.2 = Y.2)
    (f : Rational X.1.scheme Y.1.scheme 0) :
    gradedHom X Y :=
  castDegree (h ▸ degree_id X.2) f

/-- `homOfDegreeZero` is degree transport of the supplied correspondence. -/
theorem homOfDegreeZero_def {X Y : GradedCategory k} (h : X.2 = Y.2)
    (f : Rational X.1.scheme Y.1.scheme 0) :
    homOfDegreeZero h f = castDegree (h ▸ degree_id X.2) f :=
  rfl

set_option backward.privateInPublic true in
/-- The category structure determined by the graded correspondence operations. -/
@[implicit_reducible]
private def categoryOfLaws
    (assoc : ∀ {W X Y Z : GradedCategory k} (f : gradedHom W X)
      (g : gradedHom X Y) (h : gradedHom Y Z),
      gradedComp (gradedComp f g) h = gradedComp f (gradedComp g h))
    (id_comp : ∀ {X Y : GradedCategory k} (f : gradedHom X Y),
      gradedComp (gradedId X) f = f)
    (comp_id : ∀ {X Y : GradedCategory k} (f : gradedHom X Y),
      gradedComp f (gradedId Y) = f) :
    CategoryTheory.Category.{u + 1} (GradedCategory k) where
  Hom := gradedHom
  id := gradedId
  comp := gradedComp
  assoc := assoc
  id_comp := id_comp
  comp_id := comp_id

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Degree-graded rational correspondences form a category. -/
instance instCategory : CategoryTheory.Category.{u + 1} (GradedCategory k) :=
  let laws :
      (∀ {W X Y Z : GradedCategory k} (f : gradedHom W X)
        (g : gradedHom X Y) (h : gradedHom Y Z),
        gradedComp (gradedComp f g) h = gradedComp f (gradedComp g h)) ∧
      (∀ {X Y : GradedCategory k} (f : gradedHom X Y),
        gradedComp (gradedId X) f = f) ∧
      (∀ {X Y : GradedCategory k} (f : gradedHom X Y),
        gradedComp f (gradedId Y) = f) := sorry
  categoryOfLaws laws.1 laws.2.1 laws.2.2

/-- Equality identifying the tensor degree of two graded morphisms. -/
theorem degree_tensor (a₁ b₁ a₂ b₂ : ℤ) :
    (b₁ - a₁) + (b₂ - a₂) = (b₁ + b₂) - (a₁ + a₂) := by
  omega

/-- Tensor product of two graded rational correspondences. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : GradedCategory k}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  castDegree (degree_tensor X₁.2 Y₁.2 X₂.2 Y₂.2)
    (Correspondence.tensor
      (f : Rational X₁.1.scheme Y₁.1.scheme (Y₁.2 - X₁.2))
      (g : Rational X₂.1.scheme Y₂.1.scheme (Y₂.2 - X₂.2)))

/-- The graded tensor morphism is the degree transport of the correspondence tensor. -/
theorem tensorHom_def {X₁ Y₁ X₂ Y₂ : GradedCategory k}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorHom f g =
      castDegree (degree_tensor X₁.2 Y₁.2 X₂.2 Y₂.2)
        (Correspondence.tensor
          (f : Rational X₁.1.scheme Y₁.1.scheme (Y₁.2 - X₁.2))
          (g : Rational X₂.1.scheme Y₂.1.scheme (Y₂.2 - X₂.2))) :=
  rfl

/-- The associator induced by reassociation of products of schemes and addition of twists. -/
def associator (X Y Z : GradedCategory k) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) where
  hom := homOfDegreeZero (add_assoc X.2 Y.2 Z.2)
    (Correspondence.associator X.1 Y.1 Z.1).hom
  inv := homOfDegreeZero (add_assoc X.2 Y.2 Z.2).symm
    (Correspondence.associator X.1 Y.1 Z.1).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying scheme correspondence of the graded associator is the usual one. -/
theorem associator_hom (X Y Z : GradedCategory k) :
    (associator X Y Z).hom = homOfDegreeZero (add_assoc X.2 Y.2 Z.2)
      (Correspondence.associator X.1 Y.1 Z.1).hom :=
  rfl

/-- The scheme isomorphism underlying the graded left unitor. -/
def leftUnitorSchemeIso (X : GradedCategory k) :
    (tensorObj (tensorUnit k) X).1.scheme ≅ X.1.scheme where
  hom := CategoryTheory.Limits.prod.snd
  inv := CategoryTheory.Limits.prod.lift (CategoryTheory.Limits.terminal.from X.1.scheme)
    (𝟙 X.1.scheme)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The left unitor induced by the product with `Spec(k)`. -/
def leftUnitor (X : GradedCategory k) : tensorObj (tensorUnit k) X ≅ X where
  hom := homOfDegreeZero (zero_add X.2)
    (Correspondence.rationalGraphIso _ _ (leftUnitorSchemeIso X))
  inv := homOfDegreeZero (zero_add X.2).symm
    (Correspondence.rationalGraphIso _ _ (leftUnitorSchemeIso X).symm)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying scheme correspondence of the graded left unitor is the usual one. -/
theorem leftUnitor_hom (X : GradedCategory k) :
    (leftUnitor X).hom =
      homOfDegreeZero (zero_add X.2)
        (Correspondence.rationalGraphIso _ _ (leftUnitorSchemeIso X)) :=
  rfl

/-- The scheme isomorphism underlying the graded right unitor. -/
def rightUnitorSchemeIso (X : GradedCategory k) :
    (tensorObj X (tensorUnit k)).1.scheme ≅ X.1.scheme where
  hom := CategoryTheory.Limits.prod.fst
  inv := CategoryTheory.Limits.prod.lift (𝟙 X.1.scheme)
    (CategoryTheory.Limits.terminal.from X.1.scheme)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The right unitor induced by the product with `Spec(k)`. -/
def rightUnitor (X : GradedCategory k) : tensorObj X (tensorUnit k) ≅ X where
  hom := homOfDegreeZero (add_zero X.2)
    (Correspondence.rationalGraphIso _ _ (rightUnitorSchemeIso X))
  inv := homOfDegreeZero (add_zero X.2).symm
    (Correspondence.rationalGraphIso _ _ (rightUnitorSchemeIso X).symm)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying scheme correspondence of the graded right unitor is the usual one. -/
theorem rightUnitor_hom (X : GradedCategory k) :
    (rightUnitor X).hom =
      homOfDegreeZero (add_zero X.2)
        (Correspondence.rationalGraphIso _ _ (rightUnitorSchemeIso X)) :=
  rfl

/-- The braiding induced by swapping the two scheme factors. -/
def braiding (X Y : GradedCategory k) : tensorObj X Y ≅ tensorObj Y X where
  hom := homOfDegreeZero (add_comm X.2 Y.2) (Correspondence.braiding X.1 Y.1).hom
  inv := homOfDegreeZero (add_comm X.2 Y.2).symm (Correspondence.braiding X.1 Y.1).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The concrete tensor product, tensor unit, and coherence isomorphisms on graded
rational Chow correspondences. -/
@[implicit_reducible]
noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct (GradedCategory k) where
  tensorObj := tensorObj
  whiskerLeft := fun X {_ _} f ↦ tensorHom (𝟙 X) f
  whiskerRight := fun {_ _} f Y ↦ tensorHom f (𝟙 Y)
  tensorHom := fun f g ↦ GradedCategory.tensorHom f g
  tensorUnit := tensorUnit k
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-- The concrete graded tensor operations satisfy the monoidal coherence laws. -/
@[implicit_reducible]
noncomputable instance instMonoidalCategory : MonoidalCategory (GradedCategory k) :=
  let laws :
      (∀ {X₁ Y₁ X₂ Y₂ : GradedCategory k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
        f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)) ∧
      (∀ X₁ X₂ : GradedCategory k, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)) ∧
      (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : GradedCategory k} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
        (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)) ∧
      (∀ X Y : GradedCategory k, X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)) ∧
      (∀ X Y : GradedCategory k, 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)) ∧
      (∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedCategory k} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
        (f₃ : X₃ ⟶ Y₃), ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
          (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))) ∧
      (∀ {X Y : GradedCategory k} (f : X ⟶ Y), 𝟙_ (GradedCategory k) ◁ f ≫ (λ_ Y).hom =
        (λ_ X).hom ≫ f) ∧
      (∀ {X Y : GradedCategory k} (f : X ⟶ Y), f ▷ 𝟙_ (GradedCategory k) ≫ (ρ_ Y).hom =
        (ρ_ X).hom ≫ f) ∧
      (∀ W X Y Z : GradedCategory k,
        (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
          (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) ∧
      (∀ X Y : GradedCategory k, (α_ X (𝟙_ (GradedCategory k)) Y).hom ≫ X ◁ (λ_ Y).hom =
        (ρ_ X).hom ▷ Y) := sorry
  { toMonoidalCategoryStruct := instMonoidalCategoryStruct
    tensorHom_def := laws.1
    id_tensorHom_id := laws.2.1
    tensorHom_comp_tensorHom := laws.2.2.1
    whiskerLeft_id := laws.2.2.2.1
    id_whiskerRight := laws.2.2.2.2.1
    associator_naturality := laws.2.2.2.2.2.1
    leftUnitor_naturality := laws.2.2.2.2.2.2.1
    rightUnitor_naturality := laws.2.2.2.2.2.2.2.1
    pentagon := laws.2.2.2.2.2.2.2.2.1
    triangle := laws.2.2.2.2.2.2.2.2.2 }

set_option maxHeartbeats 1000000 in
/-- The factor-swap graph correspondence makes the graded correspondence category
symmetric. -/
instance instSymmetricCategory : SymmetricCategory (GradedCategory k) :=
  let laws :
      (∀ (X : GradedCategory k) {Y Z : GradedCategory k} (f : Y ⟶ Z),
        X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X) ∧
      (∀ {X Y : GradedCategory k} (f : X ⟶ Y) (Z : GradedCategory k),
        f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f) ∧
      (∀ X Y Z : GradedCategory k,
        (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
          ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫
            (Y ◁ (braiding X Z).hom)) ∧
      (∀ X Y Z : GradedCategory k,
        (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
          (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫
            ((braiding X Z).hom ▷ Y)) ∧
      (∀ X Y : GradedCategory k,
        (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y)) := sorry
  let ⟨hRight, hLeft, hForward, hReverse, hSymmetry⟩ := laws
  { braiding := braiding
    braiding_naturality_right := hRight
    braiding_naturality_left := hLeft
    hexagon_forward := hForward
    hexagon_reverse := hReverse
    symmetry := hSymmetry }

end GradedCategory

end AlgebraicGeometry.Correspondence
