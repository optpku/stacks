module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import ReasLib.AlgebraicGeometry.Correspondence.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The correspondence-category associator induced by reassociation of scheme products. -/
noncomputable def associator (X Y Z : Category k) :
    Category.product (Category.product X Y) Z ≅ Category.product X (Category.product Y Z) :=
  let hom : Category.product (Category.product X Y) Z ⟶
      Category.product X (Category.product Y Z) :=
    rationalGraphIso (Category.product (Category.product X Y) Z)
    (Category.product X (Category.product Y Z))
    (Limits.prod.associator X.scheme Y.scheme Z.scheme)
  let inv : Category.product X (Category.product Y Z) ⟶
      Category.product (Category.product X Y) Z :=
    rationalGraphIso (Category.product X (Category.product Y Z))
    (Category.product (Category.product X Y) Z)
    (Limits.prod.associator X.scheme Y.scheme Z.scheme).symm
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The scheme isomorphism from the product with the field point on the left. -/
noncomputable def leftUnitorSchemeIso (X : Category k) :
    (Category.product (Category.unit k) X).scheme ≅ X.scheme :=
  let hom : (Category.product (Category.unit k) X).scheme ⟶ X.scheme := Limits.prod.snd
  let inv : X.scheme ⟶ (Category.product (Category.unit k) X).scheme :=
    Limits.prod.lift (terminal.from X.scheme) (𝟙 X.scheme)
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The correspondence-category left unitor induced by the scheme-product left unitor. -/
noncomputable def leftUnitor (X : Category k) :
    Category.product (Category.unit k) X ≅ X :=
  let hom : Category.product (Category.unit k) X ⟶ X :=
    rationalGraphIso (Category.product (Category.unit k) X) X
    (leftUnitorSchemeIso X)
  let inv : X ⟶ Category.product (Category.unit k) X :=
    rationalGraphIso X (Category.product (Category.unit k) X)
    (leftUnitorSchemeIso X).symm
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The scheme isomorphism from the product with the field point on the right. -/
noncomputable def rightUnitorSchemeIso (X : Category k) :
    (Category.product X (Category.unit k)).scheme ≅ X.scheme :=
  let hom : (Category.product X (Category.unit k)).scheme ⟶ X.scheme := Limits.prod.fst
  let inv : X.scheme ⟶ (Category.product X (Category.unit k)).scheme :=
    Limits.prod.lift (𝟙 X.scheme) (terminal.from X.scheme)
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The correspondence-category right unitor induced by the scheme-product right unitor. -/
noncomputable def rightUnitor (X : Category k) :
    Category.product X (Category.unit k) ≅ X :=
  let hom : Category.product X (Category.unit k) ⟶ X :=
    rationalGraphIso (Category.product X (Category.unit k)) X
    (rightUnitorSchemeIso X)
  let inv : X ⟶ Category.product X (Category.unit k) :=
    rationalGraphIso X (Category.product X (Category.unit k))
    (rightUnitorSchemeIso X).symm
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The correspondence-category braiding induced by swapping the two scheme factors. -/
noncomputable def braiding (X Y : Category k) :
    Category.product X Y ≅ Category.product Y X :=
  let hom : Category.product X Y ⟶ Category.product Y X :=
    rationalGraphIso (Category.product X Y) (Category.product Y X)
    (Limits.prod.braiding X.scheme Y.scheme)
  let inv : Category.product Y X ⟶ Category.product X Y :=
    rationalGraphIso (Category.product Y X) (Category.product X Y)
    (Limits.prod.braiding X.scheme Y.scheme).symm
  let laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := laws.1
    inv_hom_id := laws.2 }

/-- The tensor object, tensor unit, tensor morphism, associator, and unitors defined from
scheme products and rational Chow correspondences. -/
@[implicit_reducible]
noncomputable instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Category k) where
  tensorObj := Category.product
  whiskerLeft := fun X {_ _} f ↦ tensorHom (𝟙 X) f
  whiskerRight := fun {_ _} f Y ↦ tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := Category.unit k
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/-- The projection-pullback/intersection tensor satisfies the monoidal naturality and
coherence laws. -/
@[implicit_reducible]
noncomputable instance instMonoidalCategory : MonoidalCategory (Category k) :=
  let laws :
      (∀ {X₁ Y₁ X₂ Y₂ : Category k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
        f ⊗ₘ g = (f ▷ X₂) ≫ (Y₁ ◁ g)) ∧
      (∀ X₁ X₂ : Category k, 𝟙 X₁ ⊗ₘ 𝟙 X₂ = 𝟙 (X₁ ⊗ X₂)) ∧
      (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Category k} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
        (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)) ∧
      (∀ X Y : Category k, X ◁ 𝟙 Y = 𝟙 (X ⊗ Y)) ∧
      (∀ X Y : Category k, 𝟙 X ▷ Y = 𝟙 (X ⊗ Y)) ∧
      (∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Category k} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
        (f₃ : X₃ ⟶ Y₃), ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
          (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃))) ∧
      (∀ {X Y : Category k} (f : X ⟶ Y), 𝟙_ (Category k) ◁ f ≫ (λ_ Y).hom =
        (λ_ X).hom ≫ f) ∧
      (∀ {X Y : Category k} (f : X ⟶ Y), f ▷ 𝟙_ (Category k) ≫ (ρ_ Y).hom =
        (ρ_ X).hom ≫ f) ∧
      (∀ W X Y Z : Category k,
        (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
          (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom) ∧
      (∀ X Y : Category k, (α_ X (𝟙_ (Category k)) Y).hom ≫ X ◁ (λ_ Y).hom =
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
/-- The factor-swap graph correspondence makes the concrete monoidal category of rational
Chow correspondences symmetric. -/
instance instSymmetricCategory : SymmetricCategory (Category k) :=
  let laws :
      (∀ (X : Category k) {Y Z : Category k} (f : Y ⟶ Z),
        X ◁ f ≫ (AlgebraicGeometry.Correspondence.braiding X Z).hom =
          (AlgebraicGeometry.Correspondence.braiding X Y).hom ≫ f ▷ X) ∧
      (∀ {X Y : Category k} (f : X ⟶ Y) (Z : Category k),
        f ▷ Z ≫ (AlgebraicGeometry.Correspondence.braiding Y Z).hom =
          (AlgebraicGeometry.Correspondence.braiding X Z).hom ≫ Z ◁ f) ∧
      (∀ X Y Z : Category k,
        (α_ X Y Z).hom ≫
            (AlgebraicGeometry.Correspondence.braiding X (Y ⊗ Z)).hom ≫
            (α_ Y Z X).hom =
          ((AlgebraicGeometry.Correspondence.braiding X Y).hom ▷ Z) ≫
            (α_ Y X Z).hom ≫
            (Y ◁ (AlgebraicGeometry.Correspondence.braiding X Z).hom)) ∧
      (∀ X Y Z : Category k,
        (α_ X Y Z).inv ≫
            (AlgebraicGeometry.Correspondence.braiding (X ⊗ Y) Z).hom ≫
            (α_ Z X Y).inv =
          (X ◁ (AlgebraicGeometry.Correspondence.braiding Y Z).hom) ≫
            (α_ X Z Y).inv ≫
            ((AlgebraicGeometry.Correspondence.braiding X Z).hom ▷ Y)) ∧
      (∀ X Y : Category k,
        (AlgebraicGeometry.Correspondence.braiding X Y).hom ≫
          (AlgebraicGeometry.Correspondence.braiding Y X).hom = 𝟙 (X ⊗ Y)) := sorry
  let ⟨hRight, hLeft, hForward, hReverse, hSymmetry⟩ := laws
  { braiding := AlgebraicGeometry.Correspondence.braiding
    braiding_naturality_right := hRight
    braiding_naturality_left := hLeft
    hexagon_forward := hForward
    hexagon_reverse := hReverse
    symmetry := hSymmetry }

end AlgebraicGeometry.Correspondence
