module

public import ReasLib.Algebra.PolynomialTower
public import ReasLib.Algebra.PolynomialSite.Resolution

/-!
# Functorial standard polynomial resolutions

For an injective map in a ring tower, the standard resolutions form polynomial
squares. Tensoring their second algebras with the intermediate ring gives an
augmented simplicial polynomial algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open Algebra.PolynomialSite

noncomputable section

universe u

namespace Algebra.PolynomialTower

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The algebra structure on the second algebra induced by the horizontal map of a square. -/
@[reducible] def algebraPQ (X : PolynomialTower A B C) : Algebra (P X) (Q X) :=
  (toQ X).hom.toRingHom.toAlgebra

end Algebra.PolynomialTower

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The degreewise standard polynomial resolution of the intermediate algebra. -/
abbrev standardP (n : SimplexCategoryᵒᵖ) : Type u :=
  (standardAugmented A B).left.obj n

/-- The degreewise standard polynomial resolution of the target over the initial ring. -/
abbrev standardQ (n : SimplexCategoryᵒᵖ) : Type u :=
  (standardAugmented A C).left.obj n

/-- The map of algebras under the initial ring induced by the tower map. -/
def underHom : (CommRingCat.of A).mkUnder B ⟶ (CommRingCat.of A).mkUnder C :=
  Under.homMk (CommRingCat.ofHom (algebraMap B C)) (by
    ext a
    exact (IsScalarTower.algebraMap_apply A B C a).symm)

/-- The map of standard augmented resolutions induced by the tower map. -/
def standardFunctoriality : standardAugmented A B ⟶ standardAugmented A C :=
  (SimplicialObject.Augmented.whiskeringObj (Under (CommRingCat.of A))
      (CommAlgCat.{u} A) (commAlgCatEquivUnder (CommRingCat.of A)).inverse).map
    ((evaluation (CommRingCat.of A)).map (underHom A B C))

/-- The degreewise functorial map between standard resolutions. -/
def functorialityApp (n : SimplexCategoryᵒᵖ) :
    (standardAugmented A B).left.obj n ⟶ (standardAugmented A C).left.obj n :=
  (standardFunctoriality A B C).left.app n

/-- The target standard term is an algebra over the source term via functoriality. -/
@[reducible] instance instAlgebraPQ (n : SimplexCategoryᵒᵖ) :
    Algebra (standardP A B n) (standardQ A C n) :=
  (functorialityApp A B C n).hom.toRingHom.toAlgebra

/-- Functoriality of standard resolutions commutes with their augmentations. -/
theorem standardFunctoriality_augmentation (n : SimplexCategoryᵒᵖ) :
    (standardHom A B).app n ≫ CommAlgCat.ofHom (IsScalarTower.toAlgHom A B C) =
      functorialityApp A B C n ≫ (standardHom A C).app n := sorry

/-- An injective tower map makes each target standard term polynomial over the source term. -/
theorem isPolynomial_standardQ_over_standardP (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial (standardP A B n) (standardQ A C n) := sorry

/-- The standard augmentation square in each degree is a polynomial square. -/
@[reducible] def triple (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    PolynomialTower A B C :=
  ⟨{ left := { left := (standardAugmented A B).left.obj n
               right := (standardAugmented A C).left.obj n
               hom := functorialityApp A B C n }
     right := ⟨⟨⟩⟩
     hom := Arrow.homMk ((standardHom A B).app n) ((standardHom A C).app n)
       (standardFunctoriality_augmentation A B C n) },
    standard_isPolynomial A B n,
    isPolynomial_standardQ_over_standardP A B C n h_inj⟩

/-- The first algebra of the standard square is the source standard term. -/
theorem triple_P (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    ((triple A B C n h_inj).P : Type u) = standardP A B n := rfl

/-- The second algebra of the standard square is the target standard term. -/
theorem triple_Q (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    ((triple A B C n h_inj).Q : Type u) = standardQ A C n := rfl

/-- Simplicial operators induce morphisms of standard polynomial squares. -/
def tripleMap {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (h_inj : Function.Injective (algebraMap B C)) :
    triple A B C n h_inj ⟶ triple A B C m h_inj :=
  ObjectProperty.homMk (Over.homMk
    (Arrow.homMk ((standardAugmented A B).left.map φ)
      ((standardAugmented A C).left.map φ)
      ((standardFunctoriality A B C).left.naturality φ)) (by
        apply Arrow.hom_ext
        · change (standardAugmented A B).left.map φ ≫ (standardHom A B).app m =
            (standardHom A B).app n
          exact ((standardHom A B).naturality φ).trans (Category.comp_id _)
        · change (standardAugmented A C).left.map φ ≫ (standardHom A C).app m =
            (standardHom A C).app n
          exact ((standardHom A C).naturality φ).trans (Category.comp_id _)))

/-- Identity operators induce identity morphisms of standard squares. -/
theorem tripleMap_id (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    tripleMap A B C (𝟙 n) h_inj = 𝟙 (triple A B C n h_inj) := sorry

/-- Composition of operators is preserved by the maps of standard squares. -/
theorem tripleMap_comp {n m k : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (ψ : m ⟶ k)
    (h_inj : Function.Injective (algebraMap B C)) :
    tripleMap A B C (φ ≫ ψ) h_inj =
      tripleMap A B C φ h_inj ≫ tripleMap A B C ψ h_inj := sorry

/-- The standard polynomial squares form a simplicial object. -/
def tripleSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (PolynomialTower A B C) where
  obj n := triple A B C n h_inj
  map φ := tripleMap A B C φ h_inj
  map_id n := tripleMap_id A B C n h_inj
  map_comp φ ψ := tripleMap_comp A B C φ ψ h_inj

/-- Evaluation of the simplicial standard square gives its degreewise construction. -/
theorem tripleSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (tripleSimplicial A B C h_inj).obj n = triple A B C n h_inj := rfl

/-- Reversing the standard polynomial squares gives a cosimplicial object of the opposite category. -/
def tripleCosimplicial (h_inj : Function.Injective (algebraMap B C)) :
    CosimplicialObject (PolynomialTower A B C)ᵒᵖ :=
  (tripleSimplicial A B C h_inj).rightOp

/-- The cosimplicial standard square evaluates to the opposite of its simplicial term. -/
theorem tripleCosimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategory) :
    (tripleCosimplicial A B C h_inj).obj n =
      Opposite.op (triple A B C (Opposite.op n) h_inj) := rfl

/-- Tensor base change of a standard square, with its augmentation to the target. -/
def barQOver (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    PolynomialOver B C :=
  PolynomialTower.tensorOverBase (triple A B C n h_inj)

/-- The tensor of the target standard term with the intermediate ring over the source term. -/
abbrev barQ (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) : Type u :=
  (barQOver A B C n h_inj).obj.left

/-- Tensor base change of a standard square is polynomial over the intermediate ring. -/
theorem isPolynomial_barQ (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial B (barQ A B C n h_inj) :=
  (barQOver A B C n h_inj).property

/-- The tensor base changes of standard squares form a simplicial algebra. -/
def barQSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (CommAlgCat.{u} B) :=
  tripleSimplicial A B C h_inj ⋙ PolynomialTower.forgetToOverB A B C ⋙
    ObjectProperty.ι _ ⋙ Over.forget (CommAlgCat.of B C)

/-- Each term of the tensor simplicial algebra is the source of its tensor augmentation. -/
theorem barQSimplicial_obj (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQSimplicial A B C h_inj).obj n = (barQOver A B C n h_inj).obj.left := rfl

/-- Tensor augmentations commute with the simplicial operators of standard squares. -/
theorem barQHom_naturality (h_inj : Function.Injective (algebraMap B C))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (barQSimplicial A B C h_inj).map φ ≫ (barQOver A B C m h_inj).obj.hom =
      (barQOver A B C n h_inj).obj.hom ≫
        ((const (CommAlgCat.{u} B)).obj (CommAlgCat.of B C)).map φ := sorry

/-- The canonical tensor augmentations define an augmentation of simplicial algebras. -/
def barQHom (h_inj : Function.Injective (algebraMap B C)) :
    barQSimplicial A B C h_inj ⟶
      (const (CommAlgCat.{u} B)).obj (CommAlgCat.of B C) where
  app n := (barQOver A B C n h_inj).obj.hom
  naturality _ _ φ := barQHom_naturality A B C h_inj φ

/-- The augmentation of the tensor simplicial algebra is its tensor augmentation in each degree. -/
theorem barQHom_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQHom A B C h_inj).app n = (barQOver A B C n h_inj).obj.hom := rfl

/-- The canonical tensor augmentation is a polynomial simplicial resolution of the target. -/
instance isResolution_barQHom (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barQHom A B C h_inj) := sorry

end Algebra.CotangentComplex
